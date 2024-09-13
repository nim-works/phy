## Implements the core execution loop of the VM, as well as the
## `VmThread <#VmThread>`_ API.

import
  vm/[
    utils,
    vmalloc,
    vmenv,
    vmspec,
    vmtypes
  ]

type
  ErrorCode* = enum
    ecIllegalAccess  ## trying to access memory not accessible to the VM
    ecIllegalProc    ## not a valid procedure address
    ecStackOverflow  ## out of stack memory
    ecStackUnderflow ## to little stack memory
    ecIllegalGrow    ## improper grow operation
    ecTypeError      ## type error
    ecCallbackError  ## a fatal error ocurred within a callback
    ecUnreachable    ## an 'unreachable' instruction was executed

  YieldReasonKind* = enum
    yrkDone
      ## the thread sucessfully finished execution
    yrkError
      ## an error occurred. The thread cannot resume
    yrkUnhandledException
      ## an exception was raised an not handled. The thread cannot resume
    yrkStubCalled
      ## a procedure stub was called. The stub has to be resolved before
      ## continuing execution
    yrkUser
      ## some user-specified yield reason. Usually used for implementing
      ## syscalls

  YieldReason* = object
    ## The result of a VM invocation. Describes why the execution stopped.
    case kind*: YieldReasonKind:
    of yrkDone:
      typ*: TypeId        ## the return value's type (void indicates "none")
      result*: Value
    of yrkError:
      error*: ErrorCode
    of yrkUnhandledException:
      exc*: Value         ## the value passed to the raise instruction
    of yrkStubCalled:
      stub*: ProcIndex    ## the procedure that is a stub
    of yrkUser:
      reason*: int
      args*: int          ## the number of stack operands that need to be
                          ## popped

  Frame* = object
    ## Call stack frame.
    prc: ProcIndex
    comesFrom: PrgCtr ## caller PC
    start: int        ## first local
    sp: uint          ## top of stack on call entry

  VmThread* = object
    ## A thread of execution. Stores all per-thread state.
    stack: seq[Value]  ## operand stack
    locals: seq[Value]
    frames: seq[Frame]

    sp: uint       ## stack pointer; current top of stack
    stackEnd: uint ## upper bound of stack memory

    pc: PrgCtr

proc `=copy`*(x: var VmThread, y: VmThread) {.error.}

# the validation layer makes sure that all operations are legal, we don't need
# any runtime checks! (as long as the execution loop is implemented correctly,
# of course)
when not defined(debug):
  {.push checks: off.}

func signExtend*(val: uint64, shift: int8): uint64 {.inline.} =
  cast[uint64](ashr(cast[int64](val shl shift), shift))

proc findEh(c: VmEnv, t: VmThread, at: PrgCtr, frame: int): (int, uint32) =
  ## Searches for the EH instruction that is associated with `at`, starting in
  ## the call frame `frame`. The call stack is walked upwards until either an
  ## EH instruction is found or there are no more frames.
  ##
  ## On success, the target call frame and EH instruction position are
  ## returned. The frame being -1 signals that no EH instruction was found.
  var
    pc = at
    frame = frame

  while frame >= 0:
    let
      prc = t.frames[frame].prc
      handlers = c[prc].eh
      offset = pc - c[prc].code.a

    # search for the instruction's asscoiated exception handler:
    for i in handlers.items:
      if c.ehTable[i].src == offset:
        return (frame, c[prc].code.a + c.ehTable[i].dst)

    # no handler was found, try the above frame:
    pc = t.frames[frame].comesFrom
    dec frame

  # no handler exists
  result = (-1, 0'u32)

proc gc(c: var VmEnv, stack: seq[Value], t: VmThread) =
  ## Garbage collections for foreign references. A deferred refcounting
  ## scheme is used.
  var keepAlive: seq[ForeignRef]
  var lp = 0
  for frame in t.frames.items:
    for i in c[frame.prc].locals.items:
      if c.locals[i] == vtRef:
        let r = cast[ForeignRef](t.locals[uint32(lp) + i])
        if check(c.allocator, r):
          # keep alive for the duration of garbage collection
          c.allocator.incRef(r)
          keepAlive.add r

    lp += c.procs[frame.prc.int].locals.len

  # scan the operand stack for things looking like foreign references
  for it in stack.items:
    let r = ForeignRef(it)
    if check(c.allocator, r):
      c.allocator.incRef(r)
      keepAlive.add r

  # free everything in the ZCT that has a refcount of 0:
  for it in c.allocator.zct.items:
    c.allocator.cleanup(it)

  c.allocator.zct.setLen(0)

  # decrement the locally referenced cells again
  for it in keepAlive.items:
    c.allocator.decRef(it)

proc run*(c: var VmEnv, t: var VmThread, cl: RootRef): YieldReason {.raises: [].} =
  ## The main execution loop. Runs thread `t` until an event occurrs that
  ## reqires the VM to yield. `cl` is passed along to callbacks invocations.
  # use local variables to get around the var indirection and allow for better
  # code generation
  # IMPORTANT: don't pass any of these to var parameter, as it can prevent
  # an optimizing compiler from putting them into registers
  var
    stack: seq[Value]
    pc = t.pc
    fp = t.frames[^1].start # points to the current local head
  swap(t.stack, stack)
  defer:
    t.pc = pc
    t.stack = move stack

  # TODO: pre-allocate the operand stack on procedure entry
  # TODO: use a custom seq type for the stack; it's faster

  template imm8(): int8        = imm8(instr)
  template imm32(): int32      = imm32(instr)
  template imm32_8(): untyped  = imm32_8(instr)
  template imm32_16(): untyped = imm32_16(instr)

  template pop(typ: typedesc): untyped =
    cast[typ](stack.pop())

  template operand(x: static int): untyped =
    stack[stack.len - x]

  template push(val: untyped) =
    stack.add cast[Value](val)

  template asgn(idx: static int, val: untyped) =
    let v = val
    stack[stack.len - idx] = cast[Value](v)

  template binaryOp(op: untyped, name: untyped): untyped =
    let x = pop(name)
    op(cast[name](operand(1)), x)

  template check(cond: bool, err: static ErrorCode) =
    if unlikely(not cond):
      return YieldReason(kind: yrkError, error: err)

  template checkmem(address, len): HostPointer =
    let a = cast[VirtualAddr](address)
    var p: HostPointer
    check not checkmem(c.allocator, a, uint(len), p), ecIllegalAccess
    p

  template load(typ: typedesc) =
    asgn 1, cast[ptr typ](checkmem(operand(1).intVal + imm32(), sizeof(typ)))[]

  template store(typ: typedesc) =
    let val = pop(typ)
    cast[ptr typ](checkmem(pop(int64) + imm32(), sizeof(typ)))[] = val

  template mainLoop(label, body: untyped) =
    # a template in order to reduce visual nesting
    while true:
      block label:
        body
        continue
      # --- exception handling
      let value = stack.pop()
      # find the instruction and frame to jump to:
      let (frame, dest) = findEh(c, t, pc, t.frames.high)
      # `frame` is -1 if none was found
      if unlikely(frame < 0):
        return YieldReason(kind: yrkUnhandledException, exc: value)

      if frame != t.frames.high:
        # restore the target frame's context:
        t.sp = t.frames[frame + 1].sp
        fp = t.frames[frame].start
        # free the locals:
        t.locals.setLen(fp + c[t.frames[frame].prc].locals.len)
        t.frames.setLen(frame + 1)

      stack.add value # push the exception value to the stack (again)
      pc = dest + 1

  mainLoop exc:
    let instr = c.code[pc]
    case opcode(instr)
    of opcNop: discard
    of opcDrop:
      stack.setLen(stack.len - 1)
    of opcDup:
      stack.setLen(stack.len + 1)
      operand(1) = operand(2)
    of opcSwap:
      swap(operand(1), operand(2))
    of opcLdConst:    push c.constants[imm32()].val
    of opcLdImmInt:   push imm32().uint64
    of opcLdImmFloat: push cast[float32](imm32()).float64

    of opcGetLocal:  push t.locals[fp + imm32()]
    of opcSetLocal:  t.locals[fp + imm32()] = operand(1)
    of opcPopLocal:  t.locals[fp + imm32()] = stack.pop()
    of opcGetGlobal: push c.globals[imm32()].val

    of opcAddImm: asgn 1, operand(1).uintVal + uint64 imm32()
    of opcAddInt: asgn 1, binaryOp(`+`, uint64)
    of opcSubInt: asgn 1, binaryOp(`-`, uint64)
    of opcMulInt: asgn 1, binaryOp(`*`, uint64)
    of opcDivInt: asgn 1, binaryOp(`div`, int64)
    of opcDivU:   asgn 1, binaryOp(`div`, uint64)
    of opcModInt: asgn 1, binaryOp(`mod`, int64)
    of opcModU:   asgn 1, binaryOp(`mod`, uint64)
    of opcNegInt: asgn 1, -operand(1).intVal
    of opcOffset:
      # use unsigned integers, for overflow-safe arithmetic
      let idx = pop(uint64)
      asgn 1, operand(1).uintVal + (idx * cast[uint64](imm32()))

    of opcAddChck:
      let (b, a) = (pop(uint64), pop(uint64))
      let sign = 1'u64 shl (imm8() - 1)
      let res = signExtend(a + b, 64 - imm8())
      push res
      push ord((res xor a) >= sign and (res xor b) >= sign)
    of opcSubChck:
      let (b, a) = (pop(uint64), pop(uint64))
      let sign = 1'u64 shl (imm8() - 1)
      let res = signExtend(a - b, 64 - imm8())
      push res
      push ord((res xor a) >= sign and (res xor not b) >= sign)

    of opcBitNot:   asgn 1, not operand(1).uintVal
    of opcBitAnd:   asgn 1, binaryOp(`and`, uint64)
    of opcBitOr:    asgn 1, binaryOp(`or`,  uint64)
    of opcBitXor:   asgn 1, binaryOp(`xor`, uint64)
    of opcShr:      asgn 1, binaryOp(`shr`, uint64)
    of opcAshr:     asgn 1, binaryOp(`shr`, int64)
    of opcShl:      asgn 1, binaryOp(`shl`, uint64)
    of opcMask:
      asgn 1, operand(1).uintVal and ((1'u64 shl imm8()) - 1)
    of opcSignExtend:
      asgn 1, signExtend(operand(1).uintVal, imm8())

    of opcAddFloat: asgn 1, binaryOp(`+`, float64)
    of opcSubFloat: asgn 1, binaryOp(`-`, float64)
    of opcMulFloat: asgn 1, binaryOp(`*`, float64)
    of opcDivFloat: asgn 1, binaryOp(`/`, float64)
    of opcNegFloat: asgn 1, -operand(1).floatVal

    of opcNot:     asgn 1, ord(operand(1).intVal == 0)
    of opcEqInt:   asgn 1, binaryOp(`==`, int64)
    of opcLtInt:   asgn 1, binaryOp(`<`,  int64)
    of opcLeInt:   asgn 1, binaryOp(`<=`, int64)
    of opcLtu:     asgn 1, binaryOp(`<`,  uint64)
    of opcLeu:     asgn 1, binaryOp(`<=`, uint64)
    of opcEqFloat: asgn 1, binaryOp(`==`, float64)
    of opcLtFloat: asgn 1, binaryOp(`<`,  float64)
    of opcLeFloat: asgn 1, binaryOp(`<=`, float64)

    of opcUIntToFloat:
      if imm8() == 8: asgn 1, float64(operand(1).uintVal)
      else:           asgn 1, float64(float32(operand(1).uintVal))
    of opcFloatToUInt:
      # convert to signed int, cast, then narrow
      let width = imm8()
      var val = cast[uint64](int64(operand(1).floatVal))
      if width < 64:
        val = val and ((1'u64 shl width) - 1)
      asgn 1, val
    of opcSIntToFloat:
      if imm8() == 8: asgn 1, float64(operand(1).intVal)
      else:           asgn 1, float64(float32(operand(1).intVal))
    of opcFloatToSInt:
      let arg = operand(1).floatVal
      case imm8()
      of 8: asgn 1, int64(arg)
      of 4: asgn 1, int64(int32(arg))
      of 2: asgn 1, int64(int16(arg))
      of 1: asgn 1, int64(int8(arg))
      else: unreachable()
    of opcReinterpF32:
      asgn 1, float64(cast[float32](cast[uint32](operand(1))))
    of opcReinterpI32:
      asgn 1, uint64(cast[uint32](operand(1).floatVal.float32))
    of opcReinterpI64, opcReinterpF64:
      discard "a no-op"

    of opcLdInt8:   load(uint8)
    of opcLdInt16:  load(uint16)
    of opcLdInt32:  load(uint32)
    of opcLdInt64:  load(uint64)
    of opcLdFlt32:  load(float32)
    of opcLdFlt64:  load(float64)
    of opcWrInt8:   store(uint8)
    of opcWrInt16:  store(uint16)
    of opcWrInt32:  store(uint32)
    of opcWrInt64:  store(uint64)
    of opcWrFlt32:  store(float32)
    of opcWrFlt64:  store(float64)
    of opcWrRef:
      let val = pop(ForeignRef)
      let dst = cast[ptr ForeignRef](checkmem(pop(int64) + imm32(), 8))
      # account for self-assignment: increment before decrementing
      if val.isNonNil:   c.allocator.incRef(val)
      if dst[].isNonNil: c.allocator.decRef(dst[])
      dst[] = val
    of opcMemCopy:
      let len = pop(uint64)
      let src = pop(VirtualAddr)
      let dst = pop(VirtualAddr)
      copyMem(checkmem(dst, len), checkmem(src, len), len)
    of opcMemClear:
      let len = pop(uint64)
      let dst = pop(uint64)
      zeroMem(checkmem(dst, len), len)

    of opcJmp:
      pc += cast[PrgCtr](imm32() - 1)
    of opcBranch:
      let (rel, inv) = imm32_8()
      if (pop(int64) xor inv) == 0:
        pc += cast[PrgCtr](rel - 1)
    of opcRet:
      let top = t.frames.pop()
      # restore the stack state:
      t.locals.setLen(top.start)
      t.sp = top.sp

      if likely(t.frames.len > 0):
        # the common case: a caller frame exists
        pc = top.comesFrom
        fp = t.frames[^1].start
      else:
        let ret = c.types.returnType(c[top.prc].typ)
        if c.types[ret].kind == tkVoid:
          return YieldReason(kind: yrkDone, typ: ret)
        else:
          return YieldReason(kind: yrkDone, typ: ret, result: stack.pop())
    of opcRaise:
      break exc # start exception handling
    of opcCall, opcIndCall:
      var
        (idx, args) = imm32_16()
        prc: ProcIndex
        bias: int32
      case opcode(instr)
      of opcCall:
        prc = cast[ProcIndex](idx)
      of opcIndCall:
        let tmp = operand(1).uintVal
        check tmp > 0 and tmp < c.procs.len.uint64, ecIllegalProc
        prc = ProcIndex(tmp - 1)
        check TypeId(idx) == c[prc].typ, ecTypeError
      else:
        unreachable()

      case c[prc].kind
      of pkDefault:
        # pop the extra operands from the stack:
        stack.setLen(stack.len - bias)
        t.frames.add Frame(prc: prc, start: t.locals.len, comesFrom: pc,
                           sp: t.sp)
        pc = c[prc].code.a - 1 # -1 accounts for the following inc
        fp = t.locals.len # update the locals pointer
        t.locals.setLen(fp + c[prc].locals.len) # make space for the new locals
      of pkCallback:
        let cb = c.callbacks[c[prc].code.a]
        # pop the extra operands from the stack:
        stack.setLen(stack.len - bias)
        let res = cb(c, toOpenArray(stack, stack.len - args, stack.high), cl)
        # pop the arguments from the stack
        stack.setLen(stack.len - args)
        case res.code
        of cecNothing: discard
        of cecValue:
          push res.value
        of cecRaise:
          push res.value
          break exc # start exception handling
        of cecError:
          return YieldReason(kind: yrkError, error: ecCallbackError)
      of pkStub:
        # unlikely case
        return YieldReason(kind: yrkStubCalled, stub: prc)

    of opcExcept:
      unreachable() # never executed
    of opcUnreachable:
      return YieldReason(kind: yrkError, error: ecUnreachable)

    of opcStackAlloc:
      let next = t.sp + cast[uint32](imm32())
      check next < t.stackEnd, ecStackOverflow
      push toVirt(t.sp)
      t.sp = next
    of opcStackFree:
      let shrink = cast[uint32](imm32())
      check shrink <= t.stackEnd, ecStackUnderflow
    of opcGrow:
      check c.allocator.grow(uint pop(uint64)), ecIllegalGrow

    of opcYield:
      inc pc
      let (num, reason) = imm32_8(instr)
      return YieldReason(kind: yrkUser, reason: reason, args: num)

    inc pc

when not defined(debug):
  {.pop.} # enable checks again

# ------- VmThread API

proc initThread*(c: VmEnv, prc: ProcIndex, stack: HOslice[uint],
                 params: sink seq[Value]): VmThread =
  ## Creates a new VM thread, with `prc` as the starting procedure and `params`
  ## as the initial operand stack. `stack` is the memory region to use for the
  ## stack of the thread.
  VmThread(pc: c[prc].code.a,
           sp: stack.a,
           stackEnd: stack.b,
           stack: params,
           locals: newSeq[Value](c[prc].locals.len),
           frames: @[Frame(prc: prc)])

proc initThread*(c: VmEnv, prc: ProcIndex, stack: uint,
                 params: sink seq[Value]): VmThread =
  ## Convenience wrapper around
  ## `initThread <#initThread,VmEnv,ProcIndex,HOslice[uint],sinkseq[Value]>`_.
  initThread(c, prc, hoSlice(0'u, stack), params)

proc dispose*(c: var VmEnv, t: sink VmThread) =
  ## Cleans up and frees all VM data owned by `t`.
  # run the GC with an empty stack
  gc(c, @[], t)

func pop*(x: var VmThread): Value =
  ## Pops a value from the operand stack.
  x.stack.pop()

template `[]`*(t: VmThread, i: Natural): Frame =
  ## Returns `t`'s stack frame at index `i`.
  t.frames[i]
