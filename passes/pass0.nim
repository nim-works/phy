## Implements the translation/lowering of L0 code into VM bytecode.

import
  std/[
    tables
  ],
  passes/[
    trees,
    spec
  ],
  vm/[
    utils,
    vmenv,
    vmmodules,
    vmspec,
    vmtypes
  ]

type
  PassCtx = object
    # inputs:
    types: NodeIndex
    signatures: ptr Table[uint32, TypeId]
      ## maps signature type IDs to their VM equivalent. A pointer in order to
      ## get around unnecessary copies

    # productions:
    code: seq[Instr]
    locals: seq[ValueType]
    constants: seq[TypedValue]
    ehTable: seq[EhMapping]

    # per-procedure temporary state:
    current: int
      ## index of the current continuation
    sp: int32
      ## the local variable storing the stack pointer
    patch: seq[tuple[cont: int, instr: int]]
    ehPatch: seq[tuple[cont: int, instr: int]]
    starts: seq[int]
      ## continuation index -> instruction offset

  Type0Kind = enum
    t0kInt
    t0kUInt
    t0kFloat
  Type0 = object
    kind: Type0Kind
    size: int

  ProcResult = object
    ## The code generated for a procedure, as well as the additional resources
    ## needed for the procedure.
    code: seq[Instr]
    locals: seq[ValueType]
    ehTable: seq[EhMapping]
    constants: seq[TypedValue]

# shorten some common parameter definitions:
using
  c: var PassCtx
  tree: PackedTree[NodeKind]

func imm(n: TreeNode[NodeKind]): int32 {.inline.} =
  assert n.kind == Immediate
  cast[int32](n.val)

func id(n: TreeNode[NodeKind]): int32 {.inline.} =
  assert n.kind in {Local, Global, Proc, ProcVal}
  cast[int32](n.val)

func typ(n: TreeNode[NodeKind]): uint32 {.inline.} =
  assert n.kind == Type
  n.val

proc parseType(tree; types: NodeIndex, n: NodeIndex): Type0 =
  var n = n
  if tree[n].kind == Type:
    n = tree.child(types, tree[n].typ) # follow the indirection

  case tree[n].kind
  of Int:   Type0(kind: t0kInt, size: tree[n].val.int)
  of UInt:  Type0(kind: t0kUInt, size: tree[n].val.int)
  of Float: Type0(kind: t0kFloat, size: tree[n].val.int)
  else:     unreachable()

func instr(c; op: Opcode) =
  c.code.add Instr(InstrType(op))

func instr(cc: var PassCtx, op: Opcode, c: int8) =
  cc.code.add Instr(InstrType(op) or (c.InstrType shl instrCShift))

func instr(c; op: Opcode, a: int32) =
  c.code.add Instr(InstrType(op) or (a.InstrType shl instrAShift))

func instr(c; op: Opcode, a: int32, b: int16) =
  c.code.add Instr(InstrType(op) or (a.InstrType shl instrAShift) or
                   (b.InstrType shl instrBShift))

func instr(cc: var PassCtx, op: Opcode, a: int32, c: int8) =
  cc.code.add Instr(InstrType(op) or (a.InstrType shl instrAShift) or
                    (c.InstrType shl instrCShift))

proc addConst(c; val: Value, typ: ValueType): int32 =
  ## Adds a new constant with the given type and value to the environment.
  result = c.constants.len.int32
  # TODO: don't add duplicates
  c.constants.add TypedValue(val: val, typ: typ)

proc loadInt(c; i: BiggestInt) =
  ## Emits the load instruction for integer value `i`.
  if i in low(int32)..high(int32):
    c.instr(opcLdImmInt, int32 i) # fits into an immediate value
  else:
    c.instr(opcLdConst, c.addConst(cast[Value](i), vtInt))

proc loadFloat(c; f: float) =
  ## Emits the load instruction for float value `f`.
  let narrowed = f.float32
  if narrowed.float == f:
    # lossless conversion is possible
    c.instr(opcLdImmFloat, cast[int32](narrowed))
  else:
    c.instr(opcLdConst, c.addConst(cast[Value](f), vtFloat))

proc prepareJump(c; target: int): int32 =
  ## Returns the operand to use for a jump instruction, where `target` is the
  ## target continuation. The next emitted instruction must be the jump
  ## instruction.
  if target <= c.current:
    # backwards jump; the target continuation has a start already
    result = int32(c.starts[target] - c.code.len)
  else:
    # forward jump; fill in the target later
    result = 0
    c.patch.add (target, c.code.len)

proc jump(c; op: Opcode, target: int; extra = 0'i8) =
  ## Emits a jump-like instruction targetting the given continuation
  ## (`target`).
  let target = c.prepareJump(target)
  c.instr(op, target, extra)

proc exit(c; target: int) =
  ## Emits the jump at the end of a continuation. The jump is omitted when
  ## unnecessary.
  if target != c.current + 1:
    c.jump(opcJmp, target)

proc xjump(c; op: Opcode): int =
  ## Emits a jump-like instruction with opcode `op` and returns its
  ## instruction position.
  c.instr(op)
  result = c.code.high

proc join(c; pc: int) =
  # TODO: remove the jump/branch if it's unnecessary
  c.code[pc] = Instr(c.code[pc].InstrType or (InstrType(c.code.len - pc) shl instrAShift))

proc genExpr(c; tree; val: NodeIndex)

proc genCall(c; tree; call: NodeIndex,
             start: int, fin: BackwardsIndex) =
  ## Generates the code a call. `start` and `fin` are where the relevant parts
  ## of the list in `call` start and end, respectively.
  template numArgs(bias: int): int16 =
     int16((tree.len(call) - ord(fin)) - start - bias)

  if tree[call, start].kind == Proc:
    # it's a static call
    for it in tree.items(call, start + 1, fin):
      c.genExpr(tree, it)

    c.instr(opcCall, tree[call, start].id, numArgs(0))
  else:
    # it's an indirect call
    for it in tree.items(call, start + 2, fin):
      c.genExpr(tree, it)

    # the proc value is pushed to the stack last
    c.genExpr(tree, tree.child(call, start + 1))
    c.instr(opcIndCall, int32 c.signatures[][tree[call, start].typ],
            numArgs(1))

proc signExtend(c; typ: Type0) =
  if typ.size < 8:
    c.instr(opcSignExtend, int8(64 - (typ.size * 8)))

proc mask(c; typ: Type0) =
  if typ.size < 8:
    c.instr(opcMask, int8(typ.size * 8))

proc genBinaryOp(c; tree; op: NodeIndex,
                 i, u, f: Opcode): Type0 {.discardable.} =
  ## Generates the code for a two-operand operation, with the opcode picked
  ## based on the type.
  let (typ, a, b) = triplet(tree, op)
  result = parseType(tree, c.types, typ)
  c.genExpr(tree, a)
  c.genExpr(tree, b)
  case result.kind
  of t0kInt:   c.instr(i)
  of t0kUInt:  c.instr(u)
  of t0kFloat: c.instr(f)

proc genBinaryArithOp(c; tree; op: NodeIndex, i, u, f: Opcode) =
  ## Similar to ``genBinaryOp``, but also handles uint overflow.
  let typ = c.genBinaryOp(tree, op, i, u, f)
  if typ.kind == t0kUInt:
    # unsigned integers need to "wrap around" on overflow
    c.mask(typ)

proc genCheckedBinary(c; tree; op: NodeIndex, opc: Opcode) =
  let (typ, a, b) = triplet(tree, op)
  c.genExpr(tree, a)
  c.genExpr(tree, b)
  c.instr(opc, int8(parseType(tree, c.types, typ).size * 8))
  c.instr(opcPopLocal, tree[op, 3].id)

proc loadLocal(c; local: int32) =
  c.instr(opcGetLocal, local)
  # TODO: merge opcPopLocal + opcGetLocal into opcSetLocal, if there's no
  #       label between the two

proc genExpr(c; tree; val: NodeIndex) =
  ## Generates the code for an expression (`val`), which is ``value`` in the
  ## grammar.
  case tree[val].kind
  of IntVal:
    c.loadInt(tree.getInt(val))
  of FloatVal:
    c.loadFloat(tree.getFloat(val))
  of ProcVal:
    # turn into a procedure address by adding 1
    c.loadInt(tree[val].id + 1)
  of Copy:
    case tree[val, 0].kind
    of Local:
      c.loadLocal(tree[val, 0].id)
    of Global:
      c.instr(opcGetGlobal, tree[val, 0].id)
    else:
      unreachable()
  of Load:
    let typ = parseType(tree, c.types, tree.child(val, 0))
    c.genExpr(tree, tree.child(val, 1))
    # TODO: if the operand is an addition or subtraction with a constant
    #       value, combine the addition with the load instruction
    case typ.kind
    of t0kInt, t0kUInt:
      case typ.size
      of 1: c.instr(opcLdInt8)
      of 2: c.instr(opcLdInt16)
      of 4: c.instr(opcLdInt32)
      of 8: c.instr(opcLdInt64)
      else: unreachable()

      if typ.kind == t0kInt:
        c.signExtend(typ)
    of t0kFloat:
      case typ.size
      of 4: c.instr(opcLdFlt32)
      of 8: c.instr(opcLdFlt64)
      else: unreachable()
  of Addr:
    c.loadLocal(c.sp)
    let offset = tree.getInt(tree.child(val, 0))
    if offset > 0:
      # TODO: use ``opcAddImm`` for small values
      c.loadInt(offset)
      c.instr(opcAddInt)
  of Neg:
    let (typ, operand) = pair(tree, val)
    c.genExpr(tree, operand)
    case parseType(tree, c.types, typ).kind
    of t0kInt:   c.instr(opcNegInt)
    of t0kFloat: c.instr(opcNegFloat)
    of t0kUInt:  unreachable()
  of Add:
    c.genBinaryArithOp(tree, val, opcAddInt, opcAddInt, opcAddFloat)
  of Sub:
    c.genBinaryArithOp(tree, val, opcSubInt, opcSubInt, opcSubFloat)
  of Mul:
    c.genBinaryArithOp(tree, val, opcMulInt, opcMulInt, opcMulFloat)
  of Div:
    # no masking is necessary, since the result of unsigned division cannot
    # be larger than the inputs
    c.genBinaryOp(tree, val, opcDivInt, opcDivU, opcDivFloat)
  of Mod:
    # 'Mod' is not supported for float
    c.genBinaryOp(tree, val, opcModInt, opcModU, opcNop)
  of AddChck:
    c.genCheckedBinary(tree, val, opcAddChck)
  of SubChck:
    c.genCheckedBinary(tree, val, opcSubChck)
  of BitNot:
    let typ = parseType(tree, c.types, tree.child(val, 0))
    c.genExpr(tree, tree.child(val, 1))
    c.instr(opcBitNot)
    c.mask(typ) # discard the unused higher bits
  of BitAnd:
    let (_, a, b) = tree.triplet(val)
    c.genExpr(tree, a)
    c.genExpr(tree, b)
    c.instr(opcBitAnd)
  of BitOr:
    let (_, a, b) = tree.triplet(val)
    c.genExpr(tree, a)
    c.genExpr(tree, b)
    c.instr(opcBitOr)
  of BitXor:
    c.genBinaryArithOp(tree, val, opcBitXor, opcBitXor, opcNop)
  of Shl:
    let (typ, a, b) = triplet(tree, val)
    c.genExpr(tree, a)
    c.genExpr(tree, b)
    c.instr(opcShl)
    let t = parseType(tree, c.types, typ)
    c.mask(t) # also cut off the upper bits for signed integers
    if t.kind == t0kInt:
      c.signExtend(t)
  of Shr:
    let (typ, a, b) = triplet(tree, val)
    c.genExpr(tree, a)
    c.genExpr(tree, b)
    case parseType(tree, c.types, typ).kind
    of t0kInt:  c.instr(opcAshr)
    of t0kUInt: c.instr(opcShr)
    else:       unreachable()
  of Not:
    c.genExpr(tree, tree.child(val, 0))
    c.instr(opcNot)
  of Eq:
    c.genBinaryOp(tree, val, opcEqInt, opcEqInt, opcEqFloat)
  of Lt:
    c.genBinaryOp(tree, val, opcLtInt, opcLtu, opcLtFloat)
  of Le:
    c.genBinaryOp(tree, val, opcLeInt, opcLeu, opcLeFloat)
  of Reinterp:
    # reinterpret the bit pattern as another type
    let
      dtyp = parseType(tree, c.types, tree.child(val, 0))
      styp = parseType(tree, c.types, tree.child(val, 1))
    # sanity checks:
    assert dtyp.kind != styp.kind
    assert dtyp.size == styp.size

    c.genExpr(tree, tree.child(val, 2))
    case dtyp.kind
    of t0kInt:
      case styp.kind
      of t0kUInt:  discard "no-op"
      of t0kFloat: c.instr(opcReinterpI64)
      of t0kInt:   unreachable()
      c.signExtend(dtyp)
    of t0kUInt:
      case styp.kind
      of t0kInt:   discard "no-op"
      of t0kFloat: c.instr(opcReinterpI64)
      of t0kUInt:  unreachable()
      c.mask(dtyp)
    of t0kFloat:
      case dtyp.size
      of 8: c.instr(opcReinterpF64)
      of 4: c.instr(opcReinterpF32)
      else: unreachable()
  of Conv:
    # numeric conversion
    let
      dtyp = parseType(tree, c.types, tree.child(val, 0))
      styp = parseType(tree, c.types, tree.child(val, 1))

    c.genExpr(tree, tree.child(val, 2))
    case dtyp.kind
    of t0kInt:
      case styp.kind
      of t0kInt, t0kUInt:
        c.signExtend(dtyp)
      of t0kFloat:
        c.instr(opcFloatToSInt, int8(dtyp.size * 8))
    of t0kUInt:
      case styp.kind
      of t0kInt:
        c.mask(dtyp)
      of t0kUInt:
        # the upper bits can only be set if the source type has larger bit-
        # width than the destination
        if dtyp.size < styp.size:
          c.mask(dtyp)
      of t0kFloat:
        c.instr(opcFloatToUInt, int8(dtyp.size * 8))
    of t0kFloat:
      case styp.kind
      of t0kInt:
        c.instr(opcSIntToFloat, int8(dtyp.size * 8))
      of t0kUInt:
        c.instr(opcUIntToFloat, int8(dtyp.size * 8))
      of t0kFloat:
        if styp.size == 8 and dtyp.size == 4:
          # demote 64-bit float to 32-bit float value. Reinterpret the bits as
          # a 32-bit integer (which internally converts to a 32-bit float
          # first) and then reinterpret the result as a 32-bit float
          c.instr(opcReinterpI32)
          c.instr(opcReinterpF32)
  of Call:
    c.genCall(tree, val, 0, ^1)
  else:
    unreachable()

proc genChoice(c; tree; typ: Type0, val, choice: NodeIndex) =
  ## Generates the code for ``Choice`` tree, where `val` is the selector and
  ## `typ` the selector's type.
  if tree.len(choice) == 2:
    c.genExpr(tree, val)
    c.genExpr(tree, tree.child(choice, 0))
    case typ.kind
    of t0kInt:   c.instr(opcEqInt)
    of t0kUInt:  c.instr(opcEqInt)
    of t0kFloat: c.instr(opcEqFloat)
    c.jump(opcBranch, tree[tree.child(choice, 1), 0].imm, 1)
  else:
    let op =
      case typ.kind
      of t0kInt:   opcLeInt
      of t0kUInt:  opcLeu
      of t0kFloat: opcLeFloat

    # lower bound comparison:
    c.genExpr(tree, tree.child(choice, 0))
    c.genExpr(tree, val)
    c.instr(op)
    # if not in range, jump to the next choice:
    let x = c.xjump(opcBranch)
    # upper bound comparison:
    c.genExpr(tree, val)
    c.genExpr(tree, tree.child(choice, 1))
    c.instr(op)
    # if in range, jump to the target continuation:
    c.jump(opcBranch, tree[tree.child(choice, 2), 0].imm, 1)
    # fall through to the next choice otherwise
    c.join(x)

proc genEh(c; tree; exit: NodeIndex) =
  ## Registers an EH table entry corresponding to `exit`, if necessary.
  case tree[exit].kind
  of Unwind:
    discard "attach nothing"
  of Continue:
    # register an EH mapping:
    c.ehTable.add (c.code.high.uint32, 0'u32) # patched later
    c.ehPatch.add (tree[exit, 0].imm.int, c.ehTable.high)
  else:
    unreachable()

proc genExit(c; tree; exit: NodeIndex) =
  ## Generates the code for a continuation exit.
  case tree[exit].kind
  of Continue:
    case tree.len(exit)
    of 1:
      c.exit(tree[exit, 0].imm)
    of 2:
      # continue with argument can only mean return
      c.genExpr(tree, tree.child(exit, 1))
      c.instr(opcRet)
    else:
      unreachable()
  of Loop:
    c.jump(opcJmp, tree[exit, 0].imm)
  of Raise:
    c.genExpr(tree, tree.child(exit, 0))
    c.instr(opcRaise)
    c.genEh(tree, tree.child(exit, 1))
  of SelectBool:
    let (sel, a, b) = triplet(tree, exit)
    c.genExpr(tree, sel)
    c.jump(opcBranch, tree[a, 0].imm)
    c.exit(tree[b, 0].imm)
  of Select:
    let
      typ = parseType(tree, c.types, tree.child(exit, 0))
      val = tree.child(exit, 1) # the value to select the target with
    for it in tree.items(exit, 2, ^2):
      c.genChoice(tree, typ, val, it)
    c.exit(tree[tree.last(tree.last(exit)), 0].imm)
  of CheckedCall:
    c.genCall(tree, exit, 0, ^3)
    c.genEh(tree, tree.last(exit))
    c.exit(tree[tree.child(exit, ^2), 0].imm)
  of CheckedCallAsgn:
    c.genCall(tree, exit, 1, ^3)
    c.genEh(tree, tree.last(exit))
    c.instr(opcPopLocal, tree[exit, 0].id)
    c.exit(tree[tree.child(exit, ^2), 0].imm)
  of Unreachable:
    c.instr(opcUnreachable)
  else:
    unreachable()

proc start(c; idx: int) =
  ## Called at the start of generating code for a continuation.
  var i = 0
  # patch jump instructions:
  while i < c.patch.len:
    if c.patch[i][0] == idx:
      c.join(c.patch[i][1])
      c.patch.del(i)
    else:
      inc i

  i = 0
  # patch EH mappings:
  while i < c.ehPatch.len:
    if c.ehPatch[i][0] == idx:
      c.ehTable[c.ehPatch[i][1]].dst = c.code.len.uint16
      c.ehPatch.del(i)
    else:
      inc i

  c.starts[idx] = c.code.len
  c.current = idx

proc genStmt(c; tree; n: NodeIndex) =
  ## Generates the bytecode for a statement (`n`).
  case tree[n].kind
  of Asgn:
    c.genExpr(tree, tree.child(n, 1))
    c.instr(opcPopLocal, tree[n, 0].id)
  of Store:
    let
      (tn, a, b) = triplet(tree, n)
      typ = parseType(tree, c.types, tn)
    # TODO: if `a` is an addition/subtraction, merge its static operand into
    #       the store instruction, if possible
    c.genExpr(tree, a)
    c.genExpr(tree, b)
    let op =
      case typ.kind
      of t0kInt, t0kUInt:
        case typ.size
        of 1: opcWrInt8
        of 2: opcWrInt16
        of 4: opcWrInt32
        of 8: opcWrInt64
        else: unreachable()
      of t0kFloat:
        case typ.size
        of 4: opcWrFlt32
        of 8: opcWrFlt64
        else: unreachable()
    c.instr(op)
  of Clear:
    c.genExpr(tree, tree.child(n, 0))
    c.genExpr(tree, tree.child(n, 1))
    c.instr(opcMemClear)
  of Blit:
    c.genExpr(tree, tree.child(n, 0))
    c.genExpr(tree, tree.child(n, 1))
    c.genExpr(tree, tree.child(n, 2))
    c.instr(opcMemCopy)
  of Call:
    c.genCall(tree, n, 0, ^1)
  of Drop:
    c.genExpr(tree, tree.child(n, 0))
    c.instr(opcDrop)
  else:
    unreachable()

proc gen(c; tree; n: NodeIndex) =
  ## Generates bytecode for the given continuation.
  case tree[n].kind
  of Except:
    c.instr(opcExcept)
    # assign the passed-along value to the provided local
    c.instr(opcPopLocal, tree[n, 0].id)
  of Continuation:
    discard "no special instruction needed"
  else:
    unreachable()

  for it in tree.items(n, 2, ^2):
    genStmt(c, tree, it)

  c.genExit(tree, tree.last(n))

proc translate(tree; types, def: NodeIndex,
               signatures: Table[uint32, TypeId]): ProcResult =
  ## Translates the single procedure body `body` to VM bytecode. `types`
  ## provides the type environment.
  let (typ, locals, conts) = tree.triplet(def)

  var c = PassCtx(types: types, signatures: addr signatures)
  # allocate and setup the local variables:
  c.locals.setLen(tree.len(locals))
  for i, it in tree.pairs(locals):
    let typ = parseType(tree, c.types, it)
    c.locals[i] = (if typ.kind == t0kFloat: vtFloat else: vtInt)

  # put all parameters into locals:
  let typedef = tree.child(types, tree[typ].val.int)
  for i in countdown(tree.len(typedef) - 1, 1):
    c.instr(opcPopLocal, int32(i - 1))

  # compute the maximum amount of required stack space:
  var maxStack = 0
  for it in tree.items(conts):
    if tree.len(it) > 1: # ignore the return continuation
      maxStack = max(tree[it, 1].imm, maxStack)

  # setup the stack pointer, if one is required:
  if maxStack > 0:
    # XXX: instead of allocating the maximum amount of stack space up-front,
    #      the stack could also be grown/shrunken on a per-continuation base,
    #      which would reduce stack-space requirements in case of nested
    #      calls
    # XXX: maybe move stack-management to a higher-level IL?
    c.locals.add(vtInt)
    c.sp = c.locals.high.int32
    c.instr(opcStackAlloc, int32 maxStack)
    c.instr(opcPopLocal, c.sp)

  # generate the code for the continuations. They're expected to be in correct
  # order:
  c.starts.newSeq(tree.len(conts))
  for i, it in tree.pairs(conts):
    if tree.len(it) > 1:
      c.start(i)
      c.gen(tree, it)
    else:
      # a continuation with only a parameter list is the "return" continuation
      if tree.len(tree.child(it, 0)) == 0:
        c.start(i)
        c.instr(opcRet)

  result = ProcResult(code: c.code, locals: c.locals, ehTable: c.ehTable,
                      constants: c.constants)

proc slice[T](old, with: seq[T]): Slice[uint32] =
  old.len.uint32 .. uint32(old.len + with.len - 1)

proc hoSlice[T](old, with: seq[T]): HOslice[uint32] =
  hoSlice(old.len.uint32, uint32(old.len + with.len))

proc translate*(module: PackedTree[NodeKind]): VmModule =
  ## Translates a complete module to the VM bytecode and the associated
  ## environmental data.
  let (types, globals, procs) = module.triplet(NodeIndex(0))
  var signatures: Table[uint32, TypeId]

  for id, typ in module.pairs(types):
    case module[typ].kind
    of Int, UInt, Float:
      discard "nothing to do"
    of ProcTy:
      let start = result.types.params.len
      # the first type (i.e., return type) needs special handling:
      if module[typ, 0].kind == Void:
        result.types.params.add(tkVoid)

      # the rest must be type references:
      for it in module.items(typ, result.types.params.len - start):
        const Map = [t0kInt: tkInt, t0kUInt: tkInt, t0kFloat: tkFloat]
        result.types.params.add Map[parseType(module, types, it).kind]

      result.types.types.add start.uint32 .. result.types.params.high.uint32
      # TODO: change the lang0 grammar such that only signatures are allowed
      #       in the type section, which would result in a 1-to-1 mapping
      #       between IL type IDs and VM type IDs, making the map obsolete
      signatures[id.uint32] = result.types.types.high.TypeId
    else:
      unreachable()

  # add the defined globals to the environment:
  for def in module.items(globals):
    let (typ, val) = module.pair(def)
    result.globals.add:
      case parseType(module, types, typ).kind
      of t0kFloat:
        TypedValue(val: cast[Value](getFloat(module, val)), typ: vtFloat)
      of t0kInt, t0kUInt:
        # signedness doesn't matter here
        TypedValue(val: cast[Value](getUInt(module, val)), typ: vtInt)

  # generate the code for the procedures and add them to the environment:
  for i, def in module.pairs(procs):
    if module[def].kind == ProcDef:
      var prc = translate(module, types, def, signatures)

      if prc.constants.len > 0:
        # patch the LdConst instructions:
        for instr in prc.code.mitems:
          if instr.opcode == opcLdConst:
            let i = imm32(instr)
            instr = Instr(instr.InstrType and not(instrAMask shl instrAShift))
            instr = Instr(instr.InstrType or
                          (InstrType(i + result.constants.len) shl instrAShift))

        result.constants.add prc.constants

      result.procs.add ProcHeader(kind: pkDefault,
                                  typ: signatures[module[def, 0].typ])
      result.procs[i].code = slice(result.code, prc.code)
      result.code.add prc.code
      result.procs[i].locals = hoSlice(result.locals, prc.locals)
      result.locals.add prc.locals

      result.procs[i].eh = hoSlice(result.ehTable, prc.ehTable)
      result.ehTable.add prc.ehTable
    else:
      # must be a host procedure
      result.host.add module.getString(module.child(def, 1))

      result.procs.add ProcHeader(kind: pkCallback,
                                  typ: signatures[module[def, 0].typ])
      result.procs[i].code.a = result.host.high.uint32
