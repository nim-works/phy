## Implements a small assembler that turns a textual representation of VM
## bytecode into bytecode. Processing happens line-by-line.
##
## A line is either:
## * a directive, when starting with a dot ('.')
## * an instruction (possibly indented)
## * a comment starting with # (which is ignored)
##
## Refer to the `Directive <#Directive>`_ enum for an overview of the
## supported directives.

import
  std/[
    strutils,
    streams,
    tables
  ],
  experimental/[
    sexp_parse
  ],
  vm/[
    utils,
    vmspec,
    vmenv,
    vmtypes
  ]

type
  AssemblerError* = object of IOError
    ## An exception raised when something goes wrong during
    ## translation / line processing.

  ProcState = object
    ## All the data making up an in-progress procedure.
    typ: TypeId
    id: ProcIndex

    # productions:
    code: seq[Instr]
    locals: seq[ValueType]
    ehTable: seq[HandlerTableEntry]
    ehCode: seq[EhInstr]

    # working state:
    labels: seq[PrgCtr]
    localLookup: Table[string, int32]
    labelLookup: Table[string, int32]

  AssemblerState* = object
    stack: seq[ProcState] ## in-progress procedures

    procs: Table[string, ProcIndex]
    consts: Table[string, int32]
    globals: Table[string, int32]
    types: Table[string, TypeId]

  Directive = enum
    dirStart  = "start"  ## start a new procedure
    dirEnd    = "end"    ## close the current procedure
    dirConst  = "const"  ## define a constant
    dirGlobal = "global" ## define a global
    dirType   = "type"   ## define a type
    dirLocal  = "local"  ## define a local
    dirLabel  = "label"  ## attach a label to the next instruction
    dirEh     = "eh"     ## attach an exception handler to the previous
                         ## instruction

template expect(cond: bool, msg = "") =
  if not cond:
    {.line.}:
      raise AssemblerError.newException(msg)

# Stream helpers
# --------------

proc readChar(s: Stream, c: char, to: var string) =
  if s.peekChar() == c:
    to.add s.readChar()

proc space(s: Stream) {.discardable} =
  while s.peekChar() in {' ', '\t'}:
    discard s.readChar()

proc comment(s: Stream) =
  ## If at the start of a comment, skips to the end of the line.
  if s.peekChar() == '#':
    discard s.readChar()
  while s.peekChar() notin {'\n', '\r', '\0'}:
    discard s.readChar()

proc expectChar(s: Stream, c: char) =
  if s.readChar() != c:
    raise AssemblerError.newException("expected '" & c & "' got")

proc parseInt(s: Stream): int =
  var str = ""
  s.readChar('-', str)

  while s.peekChar() in {'0'..'9'}:
    str.add s.readChar()

  result = parseInt(str)

proc parseFloat(s: Stream): float =
  var str = ""
  s.readChar('-', str)

  while s.peekChar() in {'0'..'9', '.'}:
    str.add s.readChar()

  result = parseFloat(str)

proc ident(s: Stream): string =
  const Allowed = {'a'..'z', 'A'..'Z', '_'}
  expect s.peekChar() in Allowed, "expected identifier"
  result.add s.readChar()

  while s.peekChar() in Allowed + {'0'..'9'}:
    result.add s.readChar()

  expect result.len > 0, "expected identifier"

# SexpParser helpers
# -------------------

template scopedParser(s: Stream) =
  ## Injects a ``SexpParser`` local openend with `s`. It's closed at the end of
  ## the scope.
  let start = s.getPosition()
  var p {.inject.}: SexpParser
  p.open(s)
  defer:
    # move the stream to the correct position
    s.setPosition(start + p.offsetBase + p.bufpos)
    # **important:** do not close the parser! It would also close the stream

proc consumeSym(p: var SexpParser): string =
  result = captureCurrString(p)
  discard p.getTok() # move to the next token

proc consumeTok(p: var SexpParser): TTokKind =
  result = p.currToken
  discard p.getTok() # move to the next token

# Parsing
# -------

proc parseValue(s: Stream, typ: ValueType): Value =
  case typ
  of vtRef, vtInt: cast[Value](parseInt(s))
  of vtFloat:      cast[Value](parseFloat(s))

proc parseTypedVal(s: Stream): TypedValue =
  let typ = parseEnum[ValueType]("vt" & s.ident())
  TypedValue(typ: typ, val: s.parseValue(typ))

proc parseType(p: var SexpParser, env: var VmEnv, a: AssemblerState, allowRef: bool): TypeId =
  ## Parses the sexp type representation given by `sexp` and adds the
  ## resulting type directly to `env`.
  if p.currToken == tkSymbol:
    expect allowRef, "cannot use type reference in this context"
    return a.types[p.consumeSym()]

  expect p.currToken == tkParensLe
  p.space()
  expect p.getTok == tkSymbol

  var desc: VmType
  case p.consumeSym()
  of "Void":
    desc = VmType(kind: tkVoid)
  of "Int":
    desc = VmType(kind: TypeKind.tkInt)
  of "Float":
    desc = VmType(kind: TypeKind.tkFloat)
  of "Foreign":
    desc = VmType(kind: tkForeign)
  of "Proc":
    desc = VmType(kind: tkProc)
    var params: seq[TypeId]

    p.space()
    while p.currToken != tkParensRi:
      params.add parseType(p, env, a, true)
      p.space()

    desc.a = env.types.params.len.uint32
    desc.b = desc.a + uint32(params.len)
    env.types.params.add params
  else:
    expect false

  p.space()
  expect p.consumeTok() == tkParensRi
  if desc.kind != tkVoid:
    env.types.add(desc)
  else:
    VoidType

proc parseType(s: Stream, env: var VmEnv, a: AssemblerState): TypeId =
  ## Parses a type description provided as an S-expression from `s`. The type
  ## description is added directly to `env`.
  scopedParser(s)
  discard p.getTok() # read the first token
  result = parseType(p, env, a, false)

proc prc(a: var AssemblerState): var ProcState {.inline.} =
  a.stack[a.stack.len - 1]

proc getLabel(a: var AssemblerState, name: string): int32 =
  ## Fetches the ID of the label with the given `name`.
  result = a.prc.labelLookup.mgetOrPut(name, a.prc.labels.len.int32)
  if result == a.prc.labels.len:
    a.prc.labels.add high(PrgCtr) # register the label with a dummy value

proc parseLabel(s: Stream, a: var AssemblerState): int32 =
  getLabel(a, s.ident())

proc parseEh(s: Stream, a: var AssemblerState): seq[EhInstr] =
  ## Parses the definition of an exception handler from `s`. Exception handlers
  ## are defined using S-expressions.
  scopedParser(s)
  discard p.getTok() # get the first token
  p.space()
  expect p.getTok() == tkParensLe
  p.space()
  while p.currToken != tkParensRi:
    var instr: EhInstr
    case p.currToken
    of tkSymbol:
      expect p.consumeSym() == "End"
      instr = (ehoEnd, 0'u16)
    of tkParensLe:
      discard p.getTok()
      p.space()
      let name = p.consumeSym()
      p.space()
      let label = p.consumeSym()
      case name
      of "Subroutine":
        instr = (ehoSubroutine, uint16 getLabel(a, label))
      of "Except":
        instr = (ehoExcept, uint16 getLabel(a, label))
      else:
        expect false

      p.space()
      expect p.consumeTok() == tkParensRi
    else:
      expect false

    p.space()
    result.add instr

  expect p.consumeTok() == tkParensRi

proc parseOp(s: Stream, op: Opcode, a: var AssemblerState): Instr =
  ## Parses a the operands for a single instruction with opcode `op`.
  template makeInstr(a = 0'i32, b = 0'i16, c = 0'i8): Instr =
    Instr((op.InstrType) or
          (a.InstrType shl instrAShift) or
          (b.InstrType shl instrBShift) or
          (c.InstrType shl instrCShift))

  template instrA(): Instr =
    makeInstr(int32 s.parseInt(), 0, 0)

  template instrAB(): Instr =
    makeInstr(int32 s.parseInt(), (s.space(); int16 s.parseInt()))

  template instrAC(): Instr =
    makeInstr(int32 s.parseInt(), 0, (s.space(); int8 s.parseInt()))

  template instrC(): Instr =
    makeInstr(0, 0, int8 s.parseInt())

  case op
  of opcNop, opcDrop, opcDup, opcSwap, opcAddInt, opcSubInt, opcMulInt,
     opcDivInt, opcDivU, opcModInt, opcModU, opcNegInt, opcBitAnd, opcBitOr,
     opcBitXor, opcBitNot, opcShr, opcAshr, opcShl, opcRet, opcAddFloat,
     opcSubFloat, opcMulFloat, opcDivFloat, opcNegFloat, opcEqInt, opcLtInt,
     opcLeInt, opcLtu, opcLeu, opcEqFloat, opcLtFloat, opcLeFloat, opcNot,
     opcReinterpF32, opcReinterpF64, opcReinterpI32, opcReinterpI64, opcBegin,
     opcEnd, opcExcept, opcRaise, opcMemCopy, opcMemClear, opcGrow:
    Instr(op) # instruction with no immediate operands
  of opcAddImm, opcLdConst, opcLdImmInt, opcOffset,
     opcLdInt8, opcLdInt16, opcLdInt32, opcLdInt64, opcLdFlt32, opcLdFlt64,
     opcWrInt8, opcWrInt16, opcWrInt32, opcWrInt64, opcWrFlt32, opcWrFlt64,
     opcWrRef, opcStackAlloc, opcStackFree:
    instrA()
  of opcLeave:
    makeInstr(s.parseLabel(a), (s.space(); int16 s.parseInt()))
  of opcLdImmFloat:
    makeInstr(cast[int32](float32(s.parseFloat())))
  of opcMask, opcSignExtend, opcAddChck, opcSubChck, opcUIntToFloat,
     opcFloatToUint, opcSIntToFloat, opcFloatToSInt:
    instrC()
  of opcBranch:
    makeInstr(s.parseLabel(a), c = (s.space(); int8 s.parseInt()))
  of opcJmp, opcEnter:
    makeInstr(s.parseLabel(a))
  of opcCall:
    makeInstr(int32 a.procs[s.ident()], (s.space(); int16 s.parseInt()))
  of opcIndCall:
    instrAB()
  of opcGetLocal, opcSetLocal, opcPopLocal:
    makeInstr(a.prc.localLookup[s.ident()])
  of opcGetGlobal:
    makeInstr(a.globals[s.ident()])
  of opcYield:
    instrAC()

proc patch(prc: var ProcState, c: VmEnv) =
  ## Patches all jump instructions and prepares the content of `prc` for being
  ## added to `c`.
  for name, it in prc.labelLookup.pairs:
    expect prc.labels[it] < high(PrgCtr), "missing label: " & name

  for i, it in prc.code.mpairs:
    if it.opcode in {opcBranch, opcJmp, opcEnter, opcLeave}:
      let label = int(prc.labels[imm32(it)]) - i
      # clear out the old operand:
      it = Instr(it.InstrType and not(instrAMask shl instrAShift))
      # set the new operand value:
      it = Instr(it.InstrType or (label.InstrType shl instrAShift))

  # patch the EH code:
  for it in prc.ehCode.mitems:
    if it.opcode in {ehoExcept, ehoSubroutine}:
      it.a = prc.labels[it.a].uint16

  # patch the EH table:
  for it in prc.ehTable.mitems:
    it.instr += c.ehCode.len.uint32

proc slice[T](old, with: seq[T]): Slice[uint32] =
  old.len.uint32 .. uint32(old.len + with.len - 1)

proc hoSlice[T](old, with: seq[T]): HOslice[uint32] =
  hoSlice(old.len.uint32, uint32(old.len + with.len))

proc process*(a: var AssemblerState, line: sink string, env: var VmEnv) =
  ## Processes `line`, which must be a single line without the line terminator.
  ## An `AssemblerError <#AssemblerError>`_ or ``ValueError`` is raised when
  ## something goes wrong. The `env` might have been modified alrady in this
  ## case, but not to a point where it's in an invalid state, meaning that both
  ## `a` and `env` can continue to be used after the exception is handled.
  let s = newStringStream(line)
  s.space()
  if s.atEnd():
    discard
  elif s.peekChar() == '#':
    discard "the line is a comment"
  elif s.peekChar() == '.':
    # it's a directive
    s.expectChar('.')
    case parseEnum[Directive](s.ident())
    of dirStart:
      # .start <type-id> <name>
      var prc = ProcState(id: env.procs.len.ProcIndex)
      s.space()
      prc.typ = a.types[s.ident()]
      s.space()
      # register in the lookup table already in order to support self-
      # references
      a.procs[s.ident()] = prc.id
      env.procs.add ProcHeader() # reserve a slot already
      a.stack.add prc
    of dirEnd:
      var prc = a.stack.pop()
      patch(prc, env)
      env.procs[int prc.id] =
        ProcHeader(kind: pkDefault, typ: prc.typ,
                   code: slice(env.code, prc.code),
                   locals: hoSlice(env.locals, prc.locals),
                   eh: hoSlice(env.ehTable, prc.ehTable))
      env.locals.add prc.locals
      env.code.add prc.code
      env.ehTable.add prc.ehTable
      env.ehCode.add prc.ehCode
    of dirConst:
      # .const <name> <type> <value>
      s.space()
      let name = s.ident()
      s.space()
      let id = env.constants.len
      env.constants.add parseTypedVal(s)
      a.consts[name] = int32 id
    of dirGlobal:
      # .global <name> <type> <value>
      s.space()
      let name = s.ident()
      s.space()
      let id = env.globals.len
      env.globals.add parseTypedVal(s)
      a.globals[name] = int32 id
    of dirType:
      # .type <name> <type-desc>
      s.space()
      let name = s.ident()
      s.space()
      let t = parseType(s, env, a)
      a.types[name] = t
    of dirLocal:
      # .local <name> <type>
      expect a.stack.len > 0, "only allowed in procedure"
      s.space()
      let name = s.ident()
      s.space()
      a.prc.locals.add parseEnum[ValueType]("vt" & s.ident())
      a.prc.localLookup[name] = int32 a.prc.locals.high
    of dirLabel:
      # .label <name>
      expect a.stack.len > 0, "only allowed in procedure"
      s.space()
      let id = s.parseLabel(a)
      a.prc.labels[id] = a.prc.code.len.PrgCtr
    of dirEh:
      # .eh <eh>
      expect a.stack.len > 0, "only allowed in procedure"
      let code = s.parseEh(a)
      a.prc.ehTable.add (a.prc.code.high.uint32, a.prc.ehCode.len.uint32)
      a.prc.ehCode.add code

  else:
    expect a.stack.len > 0, "instruction must be part of procedure"
    s.space()
    let op = parseEnum[Opcode]("opc" & s.ident())
    s.space()
    a.prc.code.add s.parseOp(op, a)

  s.space()
  s.comment()
  expect s.atEnd
