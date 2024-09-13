## A collection of procedures for invoking the VM, aimed at utilities and test
## runners.

import
  phy/[
    types
  ],
  vm/[
    vmalloc,
    vmenv,
    vm,
    utils
  ]

proc run*(env: var VmEnv, prc: ProcIndex, typ: SemType): string =
  ## Runs the nullary procedure with index `prc`, and returns the result
  ## rendered as a string. `typ` is the type of the resulting value.
  var thread: VmThread
  if typ.kind in ComplexTypes:
    # reserve enough stack space:
    let start = uint size(typ)
    # pass the address of the destination as the first parameter
    thread = vm.initThread(env, prc, hoSlice(start, 1024), @[Value(toVirt 0)])
  else:
    thread = vm.initThread(env, prc, 1024, @[])

  let res = run(env, thread, nil)
  env.dispose(thread)

  case res.kind
  of yrkDone:
    case typ.kind
    of tkVoid:
      # this is nonsense ('void' has no value), but it's allowed for
      # convenience
      result = "void"
    of tkUnit:
      result = "unit"
    of tkBool:
      case res.result.intVal
      of 0: result = "false: bool"
      of 1: result = "true: bool"
      else: result = "unknown(" & $res.result.intVal & "): bool"
    of tkInt:
      result = $res.result.intVal & ": int"
    of tkFloat:
      result = $res.result.floatVal & ": float"
    of tkTuple:
      # FIXME: implement this
      result = "<missing>"
    of tkError:
      unreachable()
  of yrkError:
    result = "runtime error: " & $res.error
  of yrkUnhandledException:
    result = "unhandled exception: " & $res.exc.intVal
  of yrkStubCalled, yrkUser:
    unreachable() # shouldn't happen
