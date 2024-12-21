## Implements the validation of bytecode and the various VM execution
## environment state (procedure headers, types, etc.).
##
## The validation layer makes sure that at run-time, the VM can rely on
## the code and environment being well-formed, with the only possible errors
## being guest errors (e.g., illegal memory access).

import
  std/[
    packedsets,
    strformat
  ],
  experimental/[
    results
  ],
  vm/[
    utils,
    vmspec,
    vmmodules,
    vmtypes,
    vmenv
  ]

type
  ValidationState = object
    prc: ProcIndex  ## checked procedure
    length: int     ## number of instruction in the body

    active: bool    ## whether control-flow reaches the current instruction

    stack: seq[ValueType]        ## abstract operand stack
    targets: PackedSet[PrgCtr]   ## all positions that are jumped to

  CheckResult = Result[void, string]

# error messages should answer the question: "what is wrong?"

const
  errNotForwardJump = "not a forward jump"

proc toValueType(t: VmType): ValueType =
  case t
  of tkInt:     vtInt
  of tkFloat:   vtFloat
  of tkForeign: vtRef
  of tkVoid:    unreachable()

template `[]`(m: VmModule, idx: ProcIndex): ProcHeader =
  m.procs[ord idx]

proc param(env: TypeEnv, t: TypeId, i: int): ValueType =
  toValueType(vmtypes.param(env, t, i))

proc test(a: seq|openArray, i: SomeInteger): bool =
  when i is SomeUnsignedInt:
    i < a.len.uint
  else:
    i >= 0 and i < a.len

template check(cond: bool, msg: untyped) =
  ## Helper template for easier error propagation.
  if not cond:
    return CheckResult.err(msg)

template check(res: CheckResult) =
  ## Helper template for easier error propagation.
  let tmp = res
  if tmp.isErr:
    return tmp

proc run(ctx: var ValidationState, env: VmModule, pos: PrgCtr, instr: Instr
        ): CheckResult =
  ## * applies the operand-stack effects of instruction `instr` at `pos`
  ## * verifies that the instruction is well-formed
  ## * verifies that the various preconditions and invariants hold
  template expect(num: int) =
    check ctx.stack.len >= num, "stack underflow"

  template push(typ: ValueType) =
    ctx.stack.add typ

  template pop(typ: ValueType) =
    expect(1)
    check ctx.stack.pop() == typ, "unexpected type"

  template checked(s: seq, pos: untyped): untyped =
    let p = pos
    if test(s, pos): s[p]
    else: return CheckResult.err("index out of bounds")

  template checkedLocal(idx: int32): ValueType =
    let i = idx
    check i in 0..(env[ctx.prc].locals.len - 1), "index out of bounds"
    checked(env.locals, env[ctx.prc].locals.a + i.uint32)

  template expectEmpty() =
    check ctx.stack.len == 0, "stack is not empty"

  template jump(rel: int32) =
    ctx.active = false

  # handle jump targets:
  if pos in ctx.targets:
    expectEmpty()
    ctx.active = true

  case opcode(instr)
  of opcNop:
    discard "no op"
  of opcDrop:
    expect(1)
    discard ctx.stack.pop()
  of opcDup:
    expect(1)
    push(ctx.stack[^1])
  of opcSwap:
    expect(2)
    swap(ctx.stack[^1], ctx.stack[^2])
  of opcLdConst:
    push(checked(env.constants, imm32(instr)).typ)
  of opcLdImmInt:
    push(vtInt)
  of opcLdImmFloat:
    push(vtFloat)
  of opcGetLocal:
    push(checkedLocal(imm32(instr)))
  of opcSetLocal:
    let typ = checkedLocal(imm32(instr))
    pop(typ)
    push(typ)
  of opcPopLocal:
    pop(checkedLocal(imm32(instr)))
  of opcGetGlobal:
    push(checked(env.globals, imm32(instr)).typ)
  of opcAddImm:
    pop(vtInt)
    push(vtInt)
  of opcAddInt, opcSubInt, opcMulInt, opcDivInt, opcDivU, opcModInt, opcModU,
     opcBitAnd, opcBitOr, opcBitXor, opcShr, opcShl, opcEqInt, opcLtInt,
     opcLeInt, opcLeu, opcLtu, opcAshr:
    pop(vtInt)
    pop(vtInt)
    push(vtInt)
  of opcAddChck, opcSubChck:
    check imm8(instr) in 1..64, "width not in range 1..64"
    pop(vtInt); pop(vtInt)
    push(vtInt); push(vtInt)
  of opcMask, opcSignExtend:
    pop(vtInt)
    push(vtInt)
    check imm8(instr) in 0..63, "width not in range 0..63"
  of opcNegInt, opcNot, opcBitNot:
    pop(vtInt)
    push(vtInt)
  of opcAddFloat, opcSubFloat, opcMulFloat, opcDivFloat:
    pop(vtFloat); pop(vtFloat)
    push(vtFloat)
  of opcNegFloat:
    pop(vtFloat)
    push(vtFloat)
  of opcOffset:
    pop(vtInt)
    pop(vtInt)
    push(vtInt)
  of opcEqFloat, opcLtFloat, opcLeFloat:
    pop(vtFloat); pop(vtFloat)
    push(vtInt)
  of opcUIntToFloat, opcSIntToFloat:
    pop(vtInt)
    push(vtFloat)
  of opcFloatToSInt, opcFloatToUint, opcReinterpI32, opcReinterpI64:
    pop(vtFloat)
    push(vtInt)
  of opcLdInt8, opcLdInt16, opcLdInt32, opcLdInt64:
    pop(vtInt)
    push(vtInt)
  of opcLdFlt32, opcLdFlt64, opcReinterpF32, opcReinterpF64:
    pop(vtInt)
    push(vtFloat)
  of opcWrInt8, opcWrInt16, opcWrInt32, opcWrInt64:
    pop(vtInt)
    pop(vtInt)
  of opcWrFlt32, opcWrFlt64:
    pop(vtFloat)
    pop(vtInt)
  of opcWrRef:
    pop(vtInt)
    pop(vtRef)
  of opcMemCopy:
    pop(vtInt)
    pop(vtInt)
    pop(vtInt)
  of opcMemClear:
    pop(vtInt)
    pop(vtInt)
  of opcJmp:
    expectEmpty()
    jump(imm32(instr))
  of opcBranch:
    let (rel, invert) = imm32_8(instr)
    check invert in {0, 1}, "'invert' flag not 0 or 1"
    pop(vtInt)
    expectEmpty()
    jump(rel)
  of opcRet:
    let expect = env.types.returnType(env[ctx.prc].typ)
    if expect != tkVoid:
      pop(toValueType expect)
    expectEmpty()
    ctx.active = false
  of opcRaise:
    pop(vtInt)
    expectEmpty()
    ctx.active = false
  of opcCall, opcIndCall:
    let (idx, num) = imm32_16(instr)
    var typ: TypeId

    case opcode(instr)
    of opcCall:
      typ = checked(env.procs, idx).typ
    of opcIndCall:
      discard checked(env.types.types, idx)
      typ = TypeId idx
      pop(vtInt) # callee
    else:
      unreachable()

    check env.types.numParams(typ) == num, "arity doesn't match"

    # pop all arguments from the stack, expecting the given kinds
    for i in 0..<num:
      pop(env.types.param(typ, num - i - 1))

    # push the return value, if any
    let ret = env.types.returnType(typ)
    if ret != tkVoid:
      push(toValueType ret)
  of opcExcept:
    check not ctx.active, "control-flow reaches 'opcExcept'"
    push(vtInt)
    ctx.active = true
  of opcUnreachable:
    ctx.active = false
  of opcStackAlloc:
    push(vtInt)
  of opcStackFree, opcGrow:
    discard
  of opcYield:
    expect(imm32(instr))
    ctx.stack.setLen ctx.stack.len-imm32(instr)

  result.initSuccess()

proc verify(ctx: ValidationState, env: VmModule, tbl: HOslice[uint32],
            code: openArray[Instr]): CheckResult =
  ## Verifies the EH table `tbl`. Code is code of the procedure the table
  ## is associated with.
  if tbl.a >= tbl.b:
    return CheckResult.ok() # EH table has no items

  check test(env.ehTable, tbl.a) and test(env.ehTable, tbl.b - 1),
        "EH table is illformed"

  for i in tbl.items:
    let (src, dst) = env.ehTable[i]
    check test(code, src), "EH table is illformed"
    check test(code, dst), "EH table is illformed"
    check dst > src, errNotForwardJump
    check code[dst].opcode == opcExcept, "target is not 'opcExcept' instruction"

  result.initSuccess()

proc verify*(hdr: ProcHeader, env: VmModule): CheckResult =
  ## Verifies that `hdr` is a valid procedure header.
  const Error = "proc header is illformed"
  case hdr.kind
  of pkDefault:
    check hdr.code.b >= hdr.code.a, Error
    check test(env.code, hdr.code.a) and test(env.code, hdr.code.b), Error
    check hdr.locals.b >= hdr.locals.a, Error
    if hdr.locals.len > 0:
      check test(env.locals, hdr.locals.a) and test(env.locals, hdr.locals.b-1),
            Error
    # the EH table is checked later
  of pkCallback:
    check test(env.names, hdr.code.a), Error
  of pkStub:
    result = CheckResult.err("stub procedures are not allowed in modules")

  check test(env.types.types, hdr.typ.uint32), "signature type is missing"
  result.initSuccess()

proc verify*(env: VmModule, prc: ProcIndex, code: openArray[Instr]): CheckResult =
  ## Verifies that the `code` belonging to procedure `prc` is valid. The
  ## associated EH table and instructions are also verified.
  var ctx = ValidationState(prc: prc, length: code.len, active: true)

  # push all parameters to the operand stack:
  for _, it in parameters(env.types, env[prc].typ):
    ctx.stack.add(toValueType it)

  # run abstract evaluation for all instructions:
  for pos, instr in code.pairs:
    let res = run(ctx, env, PrgCtr(pos), instr)
    if res.isErr:
      return CheckResult.err(fmt"at {pos}: {res.error}")

  check not ctx.active, "control-flow falls through"
  check verify(ctx, env, env[prc].eh, code) # EH table

  result.initSuccess()

proc verify*(types: TypeEnv): CheckResult =
  ## Verifies the type environment, making sure it is well-formed.
  for i, it in types.types.pairs:
    check it.a <= it.b, "illformed signature entry"
    check test(types.params, it.a), "illformed signature entry"
    check test(types.params, it.b), "illformed signature entry"

    for _, p in parameters(types, TypeId i):
      check p != tkVoid, "void is not a valid parameter type"

  result.initSuccess()

proc validate*(m: VmModule): seq[string] =
  ## Validates the full module `m`, returning a log of errors encountered.
  ## If the log is empty, the environment is valid.
  template handle(res: CheckResult) =
    let tmp = res
    if tmp.isErr:
      result.add tmp.takeErr()

  handle verify(m.types)

  # make sure the constants' types are sane:
  for it in m.constants.items:
    if it.typ notin {vtInt, vtFloat}:
      result.add fmt"{it.typ} is not valid for constant ({it})"

  # make sure the globals' types are sane:
  for it in m.globals.items:
    if it.typ notin {vtInt, vtFloat}:
      result.add fmt"{it.typ} is not valid for global ({it})"

  # check all procedure headers first:
  for i, it in m.procs.pairs:
    handle verify(it, m)

  if result.len > 0:
    # don't validate the bytecode if there were any errors so far
    return

  # check the bodies:
  for i, it in m.procs.pairs:
    if it.kind == pkDefault:
      handle verify(m, ProcIndex(i),
                    m.code.toOpenArray(it.code.a.int, it.code.b.int))

  # check the export table:
  for i, it in m.exports.pairs:
    if not test(m.names, it.name):
      result.add fmt"invalid export {i}: interface name doesn't exist"

    case it.kind
    of expGlobal:
      if not test(m.globals, it.id):
        result.add fmt"invalid export {i}: global {it.id} doesn't exist"
    of expProc:
      if not test(m.procs, it.id):
        result.add fmt"invalid export {i}: procedure {it.id} doesn't exist"
