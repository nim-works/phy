## Implements the validation of bytecode and the various VM execution
## environment state (procedure headers, types, etc.).
##
## The validation layer makes sure that at run-time, the VM can rely on
## the code and environment are well-formed, with the only possible errors
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
    vmtypes,
    vmenv
  ]

type
  Subroutine = object
    covers: Slice[PrgCtr]
    parent: int ## parent subroutine index, or -1

  ValidationState = object
    prc: ProcIndex  ## checked procedure
    length: int     ## number of instruction in the body

    active: bool    ## whether control-flow reaches the current instruction

    stack: seq[ValueType]        ## abstract operand stack
    targets: PackedSet[PrgCtr]   ## all positions that are jumped to
    subroutines: seq[Subroutine]
      ## acceleration structure for fast subroutine checks

  CheckResult = Result[void, string]

# error messages should answer the question: "what is wrong?"

const
  errSubroutineJump = "jump across subroutine boundaries"
  errNotForwardJump = "not a forward jump"
  errNotAProcType   = "type is not a proc type"

proc toValueType(t: VmType): ValueType =
  case t.kind
  of tkInt, tkProc: vtInt
  of tkFloat:       vtFloat
  of tkForeign:     vtRef
  of tkVoid:        unreachable()

proc param(env: TypeEnv, t: TypeId, i: int): ValueType =
  toValueType(env[env.params[env[t].a + i.uint32 + 1]])

proc numArgs(typ: VmType): int =
  typ.len - 1

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

proc firstPass(ctx: var ValidationState, code: openArray[Instr]): CheckResult =
  ## * gathers and validates the existing subroutines
  ## * makes sure jump targets are valid
  ## * fills the `targets` set
  template checkTarget(src: int, rel: int32) =
    check src + rel in 0..(ctx.length-1), "jump target is not valid"

  template jump(src: int, rel: int32) =
    checkTarget(src, rel)
    ctx.targets.incl PrgCtr(src + rel)

  var stack: seq[int]

  for pc, instr in code.pairs:
    case instr.opcode
    of opcJmp, opcBranch:
      jump(pc, imm32(instr))
    of opcEnter:
      checkTarget(pc, imm32(instr))
      # not a jump like the other instructions
      check code[pc + imm32(instr)].opcode == opcBegin,
            "target is not an 'opcBegin' instruction"
    of opcLeave:
      jump(pc.int32, imm32(instr))
    of opcBegin:
      stack.add ctx.subroutines.len
      # the Begin instruction is not included in the covered range
      ctx.subroutines.add Subroutine(covers: PrgCtr(pc + 1)..PrgCtr(0))
    of opcEnd:
      check stack.len > 0, "not in subroutine"
      let pos = stack.pop()
      ctx.subroutines[pos].covers.b = PrgCtr(pc)
      ctx.subroutines[pos].parent =
        if stack.len > 0: stack[^1]
        else:             -1
    else:
      discard

  check stack.len == 0, "unclosed subroutines exist"
  result.initSuccess()

proc find(ctx: ValidationState, pc: PrgCtr): int =
  for i in countdown(ctx.subroutines.high, 0):
    if pc in ctx.subroutines[i].covers:
      return i
  result = -1

proc computeDepth(ctx: ValidationState, start: PrgCtr, target: PrgCtr): int =
  ## Computes and returns the amount of subroutines a forward jump from `start`
  ## to `target` exits. If a nested subroutine is entered - which is illegal -,
  ## -1 is returned.
  if ctx.subroutines.len == 0:
    return 0

  let
    a = find(ctx, start)
    b = find(ctx, target)

  if a == b:
    return 0 # intra-subroutine jump
  elif a == -1:
    return -1 # fail fast
  else:
    var i = a
    # go upwards in hierarchy until there are no more parents
    while i != -1 and i != b:
      i = ctx.subroutines[i].parent
      inc result

    # if the subroutine `target` is part of is neither `a` nor a parent
    # thereof, it's some unrelated subroutine
    if i != b:
      result = -1

proc run(ctx: var ValidationState, env: VmEnv, pos: PrgCtr, instr: Instr
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
    check find(ctx, pos) == find(ctx, pos + rel.uint32), errSubroutineJump
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
  of opcNegInt, opcNot:
    pop(vtInt)
    push(vtInt)
  of opcAddFloat, opcSubFloat, opcMulFloat, opcDivFloat:
    pop(vtFloat); pop(vtFloat)
    push(vtFloat)
  of opcNegFloat:
    pop(vtFloat)
    push(vtFloat)
  of opcBitNot, opcOffset:
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
    pop(vtInt)
    pop(vtFloat)
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
    check find(ctx, pos) == -1, "return from within subroutine"
    let expect = env.types[env.types.returnType(env[ctx.prc].typ)]
    if expect.kind != tkVoid:
      pop(toValueType expect)
    expectEmpty()
    ctx.active = false
  of opcRaise:
    pop(vtInt)
    expectEmpty()
    ctx.active = false
  of opcCall, opcIndCall, opcIndCallCl:
    let (idx, num) = imm32_16(instr)
    var typ: TypeId

    case opcode(instr)
    of opcCall:
      typ = checked(env.procs, idx).typ
    of opcIndCall:
      check checked(env.types.types, idx).kind == tkProc, errNotAProcType
      typ = TypeId idx
      pop(vtInt) # callee
    of opcIndCallCl:
      check checked(env.types.types, idx).kind == tkProc, errNotAProcType
      typ = TypeId idx
      pop(vtInt) # callee
      pop(vtInt) # environment
    else:
      unreachable()

    check env.types[typ].numArgs() == num, "arity doesn't match"

    # pop all arguments from the stack, expecting the given kinds
    for i in 0..<num:
      pop(env.types.param(typ, num - i - 1))

    # push the return value, if any
    let ret = env.types[env.types.returnType(typ)]
    if ret.kind != tkVoid:
      push(toValueType ret)
  of opcExcept:
    check not ctx.active, "control-flow reaches 'opcExcept'"
    push(vtInt)
    ctx.active = true
  of opcBegin:
    check not ctx.active, "control-flow reaches 'opcBegin'"
    ctx.active = true
  of opcEnd:
    expectEmpty()
    ctx.active = false
  of opcEnter:
    expectEmpty()
    let rel = imm32(instr)
    check rel > 0, errNotForwardJump
    let depth = computeDepth(ctx, pos, pos + uint32(rel))
    check depth == 0, "Enter invokes out-of-context subroutine"
  of opcLeave:
    expectEmpty()
    let (rel, depth) = imm32_16(instr)
    check rel > 0, errNotForwardJump
    let actual = computeDepth(ctx, pos, pos + uint32(rel))
    check actual >= 0, "Leave jumps inside unrelated subroutine"
    check actual > 0, "Leave doesn't leave subroutine"
    check actual == depth, "specified depth doesn't match actual one"
    ctx.active = false
  of opcStackAlloc:
    push(vtInt)
  of opcStackFree, opcGrow:
    discard
  of opcYield:
    expect(imm32(instr))
    ctx.stack.setLen ctx.stack.len-imm32(instr)

  result.initSuccess()

proc verify(ctx: ValidationState, env: VmEnv, code: openArray[Instr],
            pc, start: uint32): CheckResult =
  check test(env.ehCode, start), "EH table entry is illformed"

  var pos = start
  while true:
    let (opcode, arg) = env.ehCode[pos]
    case opcode
    of ehoExcept:
      check arg > pos, errNotForwardJump
      check computeDepth(ctx, pc, arg) >= 0, errSubroutineJump
      check test(code, arg), "EH instruction is illformed"
      check code[arg].opcode == opcExcept,
            "target is not 'opcExcept' instruction"
      break
    of ehoSubroutine:
      check arg > pos, errNotForwardJump
      check computeDepth(ctx, pc, arg) >= 0, errSubroutineJump
      check(not checkedAdd(pos, 1, pos) and test(env.ehCode, pos),
            "subroutine call has no follow-up")
      check test(code, arg), "EH instruction is illformed"
      check code[arg].opcode == opcBegin,
            "target is not 'opcBegin' instruction"
    of ehoNext:
      check(not checkedAdd(pos, arg, pos) and test(env.ehCode, pos),
            "EH instruction is illformed")
    of ehoEnd: break

  result.initSuccess()

proc verify(ctx: ValidationState, env: VmEnv, tbl: HOslice[uint32],
            code: openArray[Instr]): CheckResult =
  ## Verifies the EH table `tbl`. Code is code of the procedure the table
  ## is associated with.
  if tbl.a >= tbl.b:
    return CheckResult.ok() # EH table has no items

  check test(env.ehTable, tbl.a) and test(env.ehTable, tbl.b - 1),
        "EH table is illformed"

  for i in tbl.items:
    let (offset, instr) = env.ehTable[i]
    check test(code, offset), "EH table is illformed"
    check verify(ctx, env, code, offset, instr)

  result.initSuccess()

proc verify*(hdr: ProcHeader, env: VmEnv): CheckResult =
  ## Verifies that `hdr` is a valid procedure header.
  const Error = "proc header is illformed"
  case hdr.kind
  of pkDefault:
    check hdr.code.b >= hdr.code.a, Error
    check test(env.code, hdr.code.a) and test(env.code, hdr.code.b), Error
    check hdr.locals.b > hdr.locals.a, Error
    check test(env.locals, hdr.locals.a) and test(env.locals, hdr.locals.b-1),
          Error
    # the EH table is checked later
  of pkCallback:
    check test(env.callbacks, hdr.code.a), Error
  of pkStub:
    discard

  check test(env.types.types, hdr.typ.uint32), Error
  check env.types[hdr.typ].kind == tkProc, errNotAProcType
  result.initSuccess()

proc verify*(env: VmEnv, prc: ProcIndex, code: openArray[Instr]): CheckResult =
  ## Verifies that the `code` belonging to procedure `prc` is valid. The
  ## associated EH table and instructions are also verified.
  var ctx = ValidationState(prc: prc, length: code.len, active: true)

  check firstPass(ctx, code)

  # push all parameters to the operand stack:
  for _, it in parameters(env.types, env[prc].typ):
    ctx.stack.add(toValueType env.types[it])

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
  check types.types.len > 0, "type environment is empty"
  check types[VoidType].kind == tkVoid, "void type is not valid"

  for i, it in types.types.pairs:
    let i = uint32(i)
    case it.kind
    of tkInt, tkFloat, tkForeign:
      discard "nothing to check"
    of tkVoid:
      check i == 0, "only the very first type can be a 'tkVoid'"
    of tkProc:
      check it.b > it.a, "proc type has no elements"

      for x in it.a..<it.b:
        let typ = types.params[x]
        check uint32(typ) < i, "forward reference"
        var se = {tkInt, tkFloat, tkForeign}
        if x == it.a:
          se.incl tkVoid # void is only allowed for the return type

        check types[typ].kind in se, "parameter type isn't valid"

  result.initSuccess()

proc validate*(env: VmEnv): seq[string] =
  ## Validates the full environment, returning a log of errors encountered.
  ## If the log is empty, the environment is valid.
  template handle(res: CheckResult) =
    let tmp = res
    if tmp.isErr:
      result.add tmp.takeErr()

  handle verify(env.types)

  # make sure the constants' types are sane:
  for it in env.constants.items:
    if it.typ notin {vtInt, vtFloat}:
      result.add fmt"{it.typ} is not valid for constant ({it})"

  # make sure the globals' types are sane:
  for it in env.globals.items:
    if it.typ notin {vtInt, vtFloat}:
      result.add fmt"{it.typ} is not valid for global ({it})"

  # check all procedure headers first:
  for i, it in env.procs.pairs:
    handle verify(it, env)

  if result.len > 0:
    # don't validate the bytecode if there were any errors so far
    return

  # check the bodies:
  for i, it in env.procs.pairs:
    handle verify(env, ProcIndex(i), env.code.toOpenArray(it.code.a.int, it.code.b.int))
