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
    packedsets,
    parseutils,
    strutils,
    streams,
    tables
  ],
  vm/[
    utils,
    vmspec,
    vmenv,
    vmmodules,
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
    ehTable: seq[EhMapping]

    # working state:
    labels: seq[PrgCtr]
    localLookup: Table[string, int32]
    labelLookup: Table[string, int32]

  AssemblerState* = object
    stack: seq[ProcState] ## in-progress procedures
    module: VmModule ## in-progress module

    procs: Table[string, ProcIndex]
    consts: Table[string, int32]
    globals: Table[string, int32]
    types: Table[string, TypeId]
    exports: array[ExportKind, PackedSet[uint32]]

  Directive = enum
    dirStart  = "start"  ## start a new procedure
    dirEnd    = "end"    ## close the current procedure
    dirConst  = "const"  ## define a constant
    dirGlobal = "global" ## define a global
    dirType   = "type"   ## define a type
    dirExport = "export" ## mark a procedure or global as exported
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

proc expectString(s: Stream, str: string) =
  var i = 0
  while i < str.len and s.readChar() == str[i]:
    inc i

  if i < str.len:
    raise AssemblerError.newException:
      "expected '" & str & "', got '" & str[0..i] & "'"

proc parseIntLike[T](s: Stream, _: typedesc[T]): T =
  var str = ""
  while (let c = s.peekChar(); c notin {' ', '\t', '\n', '\r', '\0'}):
    str.add s.readChar()

  var temp: BiggestInt
  if parseBiggestInt(str, temp) != str.len:
    # error; might be an integer in hex format
    if parseHex(str, temp) != str.len:
        raise ValueError.newException("expected integer value")

  # cut off too large values
  result = cast[T](temp)

proc parseFloat(s: Stream): float =
  var str = ""
  while (let c = s.peekChar(); c notin {' ', '\t', '\n', '\r', '\0'}):
    str.add s.readChar()

  expect parseFloat(str, result, 0) == str.len, "expected float value"

proc ident(s: Stream): string =
  const Allowed = {'a'..'z', 'A'..'Z', '_'}
  expect s.peekChar() in Allowed, "expected identifier"
  result.add s.readChar()

  while s.peekChar() in Allowed + {'0'..'9'}:
    result.add s.readChar()

  expect result.len > 0, "expected identifier"

# Parsing
# -------

proc parseValue(s: Stream, typ: ValueType): Value =
  case typ
  of vtRef, vtInt: parseIntLike(s, Value)
  of vtFloat:      cast[Value](parseFloat(s))

proc parseTypedVal(s: Stream): TypedValue =
  let typ = parseEnum[ValueType]("vt" & s.ident())
  TypedValue(typ: typ, val: s.parseValue(typ))

proc parseType(s: Stream, env: var TypeEnv, a: AssemblerState): TypeId =
  ## Parses a signature type from `s` and adds the type directly to `env`,
  ## returning its ID.
  s.expectChar('(')
  s.space()

  proc parseTypeName(s: Stream): TypeKind =
    let name = s.ident()
    # the type names are case insensitive
    case toLower(name)
    of "void":    tkVoid
    of "int":     tkInt
    of "float":   tkFloat
    of "foreign": tkForeign
    else:
      raise AssemblerError.newException("unknown type name: " & name)

  var params: seq[VmType]

  if s.peekChar() == ')':
    discard s.readChar() # an empt parameter list
  else:
    while true:
      params.add s.parseTypeName()
      s.space()
      if s.peekChar() == ',': # a trailing comma is allowed
        discard s.readChar()
        s.space()
      else:
        s.expectChar(')')
        break

  s.space()
  s.expectString("->")
  s.space()
  result = env.add(s.parseTypeName(), params)

proc parseInterface(s: Stream): string =
  ## Parses an interface name.
  # interface names don't need to support the whole ASCII range
  const Allowed = {'A'..'Z', 'a'..'z', '0'..'9', '_', '.', '#', '(', ')'}
  expect s.readChar() == '"', "expected '\"'"
  var c: char
  while (c = s.readChar(); c in Allowed):
    result.add c

  expect c == '"', "expected closing '\"'"

proc prc(a: var AssemblerState): var ProcState {.inline.} =
  a.stack[a.stack.len - 1]

proc getLabel(a: var AssemblerState, name: string): int32 =
  ## Fetches the ID of the label with the given `name`.
  result = a.prc.labelLookup.mgetOrPut(name, a.prc.labels.len.int32)
  if result == a.prc.labels.len:
    a.prc.labels.add high(PrgCtr) # register the label with a dummy value

proc parseLabel(s: Stream, a: var AssemblerState): int32 =
  getLabel(a, s.ident())

proc parseOp(s: Stream, op: Opcode, a: var AssemblerState): Instr =
  ## Parses the operands for a single instruction with opcode `op`.
  template makeInstr(a = 0'i32, b = 0'i16, c = 0'i8): Instr =
    Instr((op.InstrType) or
          (a.InstrType shl instrAShift) or
          (b.InstrType shl instrBShift) or
          (c.InstrType shl instrCShift))

  template instrA(): Instr =
    makeInstr(s.parseIntLike(int32), 0, 0)

  template instrAC(): Instr =
    makeInstr(s.parseIntLike(int32), 0, (s.space(); s.parseIntLike(int8)))

  template instrC(): Instr =
    makeInstr(0, 0, s.parseIntLike(int8))

  case op
  of opcNop, opcDrop, opcDup, opcSwap, opcAddInt, opcSubInt, opcMulInt,
     opcDivInt, opcDivU, opcModInt, opcModU, opcNegInt, opcBitAnd, opcBitOr,
     opcBitXor, opcBitNot, opcShr, opcAshr, opcShl, opcRet, opcAddFloat,
     opcSubFloat, opcMulFloat, opcDivFloat, opcNegFloat, opcEqInt, opcLtInt,
     opcLeInt, opcLtu, opcLeu, opcEqFloat, opcLtFloat, opcLeFloat, opcNot,
     opcReinterpF32, opcReinterpF64, opcReinterpI32, opcReinterpI64,
     opcExcept, opcUnreachable, opcRaise, opcMemCopy, opcMemClear, opcGrow:
    Instr(op) # instruction with no immediate operands
  of opcAddImm, opcLdConst, opcLdImmInt, opcOffset,
     opcLdInt8, opcLdInt16, opcLdInt32, opcLdInt64, opcLdFlt32, opcLdFlt64,
     opcWrInt8, opcWrInt16, opcWrInt32, opcWrInt64, opcWrFlt32, opcWrFlt64,
     opcWrRef, opcStackAlloc, opcStackFree:
    instrA()
  of opcLdImmFloat:
    makeInstr(cast[int32](float32(s.parseFloat())))
  of opcMask, opcSignExtend, opcAddChck, opcSubChck, opcUIntToFloat,
     opcFloatToUint, opcSIntToFloat, opcFloatToSInt:
    instrC()
  of opcBranch:
    makeInstr(s.parseLabel(a), c = (s.space(); s.parseIntLike(int8)))
  of opcJmp:
    makeInstr(s.parseLabel(a))
  of opcCall:
    makeInstr(int32 a.procs[s.ident()], (s.space(); s.parseIntLike(int16)))
  of opcIndCall:
    makeInstr(int32 a.types[s.ident()], (s.space(); s.parseIntLike(int16)))
  of opcGetLocal, opcSetLocal, opcPopLocal:
    makeInstr(a.prc.localLookup[s.ident()])
  of opcGetGlobal:
    makeInstr(a.globals[s.ident()])
  of opcYield:
    instrAC()

proc patch(prc: var ProcState) =
  ## Patches all jump instructions and prepares the content of `prc` for being
  ## added to `c`.
  for name, it in prc.labelLookup.pairs:
    expect prc.labels[it] < high(PrgCtr), "missing label: " & name

  for i, it in prc.code.mpairs:
    if it.opcode in {opcBranch, opcJmp}:
      let label = int(prc.labels[imm32(it)]) - i
      # clear out the old operand:
      it = Instr(it.InstrType and not(instrAMask shl instrAShift))
      # set the new operand value:
      it = Instr(it.InstrType or (label.InstrType shl instrAShift))

  # patch the EH table:
  for it in prc.ehTable.mitems:
    it.dst = prc.labels[it.dst].uint32

proc slice[T](old, with: seq[T]): Slice[uint32] =
  old.len.uint32 .. uint32(old.len + with.len - 1)

proc hoSlice[T](old, with: seq[T]): HOslice[uint32] =
  hoSlice(old.len.uint32, uint32(old.len + with.len))

proc process*(a: var AssemblerState, line: sink string) =
  ## Processes `line`, which must be a single line without the line terminator.
  ## An `AssemblerError <#AssemblerError>`_ or ``ValueError`` is raised when
  ## something goes wrong. After the exception is handled, `a` can continue to
  ## be used.
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
      var prc = ProcState(id: a.module.procs.len.ProcIndex)
      s.space()
      prc.typ = a.types[s.ident()]
      s.space()
      # register in the lookup table already in order to support self-
      # references
      a.procs[s.ident()] = prc.id
      a.module.procs.add ProcHeader() # reserve a slot already
      a.stack.add prc
    of dirEnd:
      var prc = a.stack.pop()
      patch(prc)
      a.module.procs[int prc.id] =
        ProcHeader(kind: pkDefault, typ: prc.typ,
                   code: slice(a.module.code, prc.code),
                   locals: hoSlice(a.module.locals, prc.locals),
                   eh: hoSlice(a.module.ehTable, prc.ehTable))
      a.module.locals.add prc.locals
      a.module.code.add prc.code
      a.module.ehTable.add prc.ehTable
    of dirConst:
      # .const <name> <type> <value>
      s.space()
      let name = s.ident()
      s.space()
      let id = a.module.constants.len
      a.module.constants.add parseTypedVal(s)
      a.consts[name] = int32 id
    of dirGlobal:
      # .global <name> <type> <value>
      s.space()
      let name = s.ident()
      s.space()
      let id = a.module.globals.len
      a.module.globals.add parseTypedVal(s)
      a.globals[name] = int32 id
    of dirType:
      # .type <name> <type-desc>
      s.space()
      let name = s.ident()
      s.space()
      let t = parseType(s, a.module.types, a)
      a.types[name] = t
    of dirExport:
      # .export <kind> <name> <interface>
      s.space()
      let kind = parseEnum[ExportKind]("exp" & s.ident())
      s.space()
      let id =
        case kind
        of expProc:   a.procs[s.ident()].uint32
        of expGlobal: a.globals[s.ident()].uint32
      expect id notin a.exports[kind], "entity was already exported"
      s.space()
      a.module.exports.add:
        Export(kind: kind, id: id, name: a.module.names.len.uint32)
      let iface = s.parseInterface()
      a.module.names.add iface
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
      # .eh <name>
      expect a.stack.len > 0, "only allowed in procedure"
      let id = s.parseLabel(a)
      a.prc.ehTable.add (a.prc.code.high.uint32, id.uint32)

  else:
    expect a.stack.len > 0, "instruction must be part of procedure"
    s.space()
    let op = parseEnum[Opcode]("opc" & s.ident())
    s.space()
    a.prc.code.add s.parseOp(op, a)

  s.space()
  s.comment()
  expect s.atEnd

proc close*(a: sink AssemblerState): VmModule =
  ## Closes the assembler and returns the built module.
  move a.module
