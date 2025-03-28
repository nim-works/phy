## A collection of procedures for invoking the VM, aimed at utilities and test
## runners.

import
  std/[
    options
  ],
  experimental/[
    sexp
  ],
  phy/[
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

proc newCons(name: sink string): SexpNode =
  newSList(@[newSSymbol(name)])

proc newCons(name: sink string, elem: sink SexpNode): SexpNode =
  newSList(@[newSSymbol(name), elem])

proc readInt(p: HostPointer, size: range[1..8]): int64 =
  copyMem(addr result, p, size)

proc readFloat64(p: HostPointer): float64 =
  copyMem(addr result, p, 8)

proc primToSexp(v: Value, typ: SemType): SexpNode =
  ## Renders the primitive value `v` of type `typ` to an S-expression.
  case typ.kind
  of tkUnit:
    newCons("TupleCons")
  of tkBool:
    case v.intVal
    of 0: newCons("False")
    of 1: newCons("True")
    else: newCons("Error", newSInt(v.intVal))
  of tkChar:
    newCons("char", newSInt(v.intVal))
  of tkInt:
    newSInt(v.intVal)
  of tkFloat:
    newSFloat(v.floatVal)
  of ComplexTypes, tkError, tkVoid:
    unreachable()

proc valueToSexp(env: var VmEnv, a: VirtualAddr, typ: SemType): SexpNode =
  ## Reads a value of the given `typ` from memory location at `a` returns its
  ## S-expression representation. The address is validated first.
  var p: HostPointer
  if checkmem(env.allocator, a, uint64 size(typ), p):
    return newCons("Error", newSString("inaccessible: " & $cast[uint](a) & ">"))

  case typ.kind
  of tkUnit:
    result = newCons("TupleCons")
  of tkBool:
    result = primToSexp(Value(readInt(p, 1)), typ)
  of tkChar:
    result = primToSexp(Value(readInt(p, 1)), typ)
  of tkInt:
    result = primToSexp(Value(readInt(p, 8)), typ)
  of tkFloat:
    result = primToSexp(cast[Value](readFloat64(p)), typ)
  of tkTuple:
    result = newCons("TupleCons")
    var offset = 0
    for i, it in typ.elems.pairs:
      result.add valueToSexp(env, VirtualAddr(a.uint64 + offset.uint64), it)
      offset += size(it)
  of tkRecord:
    result = newCons("RecordCons")
    var offset = 0
    for i, it in typ.fields.pairs:
      let mask = alignment(it.typ) - 1
      offset = (offset + mask) and not mask # align the offset
      var field = newCons("Field", newSSymbol(it.name))
      field.add valueToSexp(env, VirtualAddr(a.uint64 + offset.uint64), it.typ)
      result.add field
      offset += size(it.typ)
  of tkUnion:
    let tag = readInt(p, 8)
    if tag in 0..typ.elems.high:
      result = valueToSexp(env, VirtualAddr(a.uint64 + 8), typ.elems[tag])
    else:
      result = newCons("Error", newSString("<invalid tag: " & $tag & ">"))
  of tkProc:
    # render as an ellipsis for now. Proper rendering requires access to
    # the procedure names, which we don't have at the moment
    result = newCons("proc", newSSymbol("..."))
  of tkSeq:
    result = newCons("array")
    let
      len = readInt(p, 8)
      data = readInt(cast[HostPointer](addr p[8]), 8) + 8
    for i in 0..<len:
      result.add valueToSexp(env, VirtualAddr(data + size(typ.elems[0]) * i),
                             typ.elems[0])
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
          typ: SemType, cl: RootRef): SexpNode =
  ## Runs the nullary procedure with index `prc`, and returns the result
  ## rendered as an S-expression. `typ` is the type of the resulting value.
  var thread: VmThread
  if typ.kind in AggregateTypes:
    # reserve enough stack space for the result:
    let modified = hoSlice(stack.a + uint(size(typ)), stack.b)
    # pass the address of the destination as the first parameter
    thread = vm.initThread(env, prc, modified, @[Value(toVirt stack.a)])
  else:
    thread = vm.initThread(env, prc, stack, @[])

  let res = run(env, thread, cl)
  env.dispose(thread)

  case res.kind
  of yrkDone:
    # render the value:
    case typ.kind
    of ComplexTypes: valueToSexp(env, toVirt(0), typ)
    else:            primToSexp(res.result, typ)
  of yrkError:
    if res.error == ecUnreachable:
      newCons("Unreachable")
    else:
      newCons("Error", newSString($res.error))
  of yrkUnhandledException:
    newCons("Exception", newSInt(res.exc.intVal))
  of yrkStubCalled, yrkUser:
    unreachable() # shouldn't happen

proc run*(env: var VmEnv, stack: HOslice[uint], prc: ProcIndex,
          cl: RootRef = nil): string =
  ## Runs the nullary procedure with index `prc` and returns the VM's result
  ## formatted as an S-expression.
  var thread = vm.initThread(env, prc, stack, @[])

  let res = run(env, thread, cl)
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
