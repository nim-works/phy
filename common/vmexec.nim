## A collection of procedures for invoking the VM, aimed at utilities and test
## runners.

import
  std/[
    options,
    strutils
  ],
  phy/[
    type_rendering,
    types
  ],
  vm/[
    vmalloc,
    vmenv,
    vmmodules,
    vm,
    utils
  ]

import vm/vmtypes except tkVoid, tkInt, tkFloat, tkProc

type
  MemoryConfig* = object
    ## The guest memory configuration.
    total*: uint
    stackStart*: uint
    stackSize*: uint

proc readInt(p: HostPointer, size: range[1..8]): int64 =
  copyMem(addr result, p, size)

proc readFloat64(p: HostPointer): float64 =
  copyMem(addr result, p, 8)

proc primToString(v: Value, typ: SemType): string =
  ## Renders the primitive value `v` of `typ` type to a string.
  case typ.kind
  of tkVoid:
    # this is nonsense ('void' has no value), but it's allowed for
    # convenience
    ""
  of tkUnit:
    "()"
  of tkBool:
    case v.intVal
    of 0: "false"
    of 1: "true"
    else: "unknown(" & $v.intVal & ")"
  of tkChar:
    case v.intVal
    of ord('\n'):       "'\\n'"
    of ord('\r'):       "'\\r'"
    of ord('\''):       "'\\''"
    of ord('\\'):       "'\\\\'"
    of 32..38, 40..91, 93..127:
      "'" & $char(v.intVal) & "'"
    else:
      "'\\x" & toHex(v.intVal, 2) & "'"
  of tkInt:
    $v.intVal
  of tkFloat:
    $v.floatVal
  of ComplexTypes, tkError:
    unreachable()

proc valueToString(env: var VmEnv, a: VirtualAddr, typ: SemType): string =
  ## Reads a value of the given `typ` from memory location at `a` and renders
  ## it to a string. The address is validated first.
  var p: HostPointer
  if checkmem(env.allocator, a, uint64 size(typ), p):
    return "<inaccessible: " & $cast[uint](a) & ">"

  case typ.kind
  of tkUnit:
    result = "()"
  of tkBool:
    result = primToString(Value(readInt(p, 1)), typ)
  of tkChar:
    result = primToString(Value(readInt(p, 1)), typ)
  of tkInt:
    result = $readInt(p, 8)
  of tkFloat:
    result = $readFloat64(p)
  of tkTuple:
    result = "("
    var offset = 0
    for i, it in typ.elems.pairs:
      if i > 0:
        result.add ", "
      result.add valueToString(env, VirtualAddr(a.uint64 + offset.uint64), it)
      offset += size(it)

    if typ.elems.len == 1:
      result.add ","
    result.add ")"
  of tkUnion:
    let tag = readInt(p, 8)
    if tag in 0..typ.elems.high:
      result = valueToString(env, VirtualAddr(a.uint64 + 8), typ.elems[tag])
    else:
      result = "<invalid tag: " & $tag & ">"
  of tkProc:
    # render as an ellipsis for now. Proper rendering requires access to
    # the procedure names, which we don't have at the moment
    result.add "..."
  of tkSeq:
    result = "["
    let
      len = readInt(p, 8)
      data = readInt(cast[HostPointer](addr p[8]), 8) + 8
    for i in 0..<len:
      if i > 0:
        result.add ", "
      result.add valueToString(env, VirtualAddr(data + size(typ.elems[0]) * i),
                               typ.elems[0])
    result.add "]"
  of tkVoid, tkError:
    unreachable()

proc readMemConfig*(m: VmModule): Option[MemoryConfig] =
  ## Reads the guest memory configuration from `m` by looking for the
  ## `stack_start`, `stack_size`, and `total_memory` global variables.
  ## A default is used for the values where the respective global is
  ## not present. If the configuration is invalid, ``none`` is returned.
  var
    stackStart = 0'u64
    stackSize  = 1024'u64
    total      = stackSize

  for it in m.exports.items:
    if it.kind == expGlobal and m.globals[it.id].typ == vtInt:
      case m.names[it.name]
      of "stack_start":
        stackStart = m.globals[it.id].val.uintVal
      of "stack_size":
        stackSize = m.globals[it.id].val.uintVal
      of "total_memory":
        total = m.globals[it.id].val.uintVal

  if stackStart >= total or stackStart + stackSize > total or
      stackStart + stackSize < stackStart or
      total > high(uint):
    none MemoryConfig
  else:
    some MemoryConfig(total: uint(total),
                      stackStart: uint(stackStart),
                      stackSize: uint(stackSize))

proc run*(env: var VmEnv, stack: HOslice[uint], prc: ProcIndex,
          typ: SemType): string =
  ## Runs the nullary procedure with index `prc`, and returns the result
  ## rendered as a string. `typ` is the type of the resulting value.
  var thread: VmThread
  if typ.kind in AggregateTypes:
    # reserve enough stack space for the result:
    let modified = hoSlice(stack.a + uint(size(typ)), stack.b)
    # pass the address of the destination as the first parameter
    thread = vm.initThread(env, prc, modified, @[Value(toVirt stack.a)])
  else:
    thread = vm.initThread(env, prc, stack, @[])

  let res = run(env, thread, nil)
  env.dispose(thread)

  case res.kind
  of yrkDone:
    # render the value:
    result =
      case typ.kind
      of ComplexTypes: valueToString(env, toVirt(0), typ)
      else:            primToString(res.result, typ)

    # add the type:
    if result.len > 0:
      result.add ": "
    result.add typeToString(typ)
  of yrkError:
    result = "runtime error: " & $res.error
  of yrkUnhandledException:
    result = "unhandled exception: " & $res.exc.intVal
  of yrkStubCalled, yrkUser:
    unreachable() # shouldn't happen

proc run*(env: var VmEnv, stack: HOslice[uint], prc: ProcIndex): string =
  ## Runs the nullary procedure with index `prc` and returns the VM's result
  ## formatted as an S-expression.
  var thread = vm.initThread(env, prc, stack, @[])

  let res = run(env, thread, nil)
  env.dispose(thread)

  # render the result:
  result = "(" & substr($res.kind, 3)
  case res.kind
  of yrkDone:
    case res.typ
    of vmtypes.TypeKind.tkVoid, tkForeign:
      discard
    of vmtypes.TypeKind.tkInt:
      result.add " "
      if res.result.uintVal <= high(int64).uint64:
        # the signed and unsigned interpretation yield the same value
        result.addInt res.result.uintVal
      else:
        # output both interpretations
        result.add "(" & $res.result.uintVal & " or " & $res.result.intVal & ")"
    of vmtypes.TypeKind.tkFloat:
      result.add " " & $res.result.floatVal
  of yrkError:
    result.add " "
    result.add $res.error
  of yrkStubCalled:
    result.add " "
    result.addInt res.stub.int
  of yrkUnhandledException:
    result.add " "
    result.add $res.exc.uintVal
  of yrkUser:
    unreachable() # shouldn't happen

  result.add ")"
