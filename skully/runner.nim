## Implements the runner for VM programs compiled by `skully`.

import
  vm/[
    vm,
    vmenv,
    vmmodules,
    vmvalidation,
    utils
  ],
  skully/hostprocs

proc linkAndRun*(m: VmModule, stackSize: uint): int =
  ## Links and validiates the VM module `m`. If both steps are succesful, the
  ## procedure at the last position is run, with its return value returned by
  ## ``linkAndRun``. The procedure must have the signature ``() -> int``.

  # the memory address of the start of the stack is provided by the global with
  # ID 0
  var stackStart = m.globals[0].val.uintVal.uint

  # allocate all VM memory up-front
  var env = initVm(stackStart + stackSize, stackStart + stackSize)
  link(env, hostProcedures(), [m])

  let errors = validate(env)
  if errors.len > 0:
    echo "---- Validation failed:"
    for it in errors.items:
      echo it

    # XXX: meh, this needs some proper error handling, so that a validation
    #      failure can be distinguished from, e.g., a program error
    return 1

  # XXX: once VM modules support exports, run the procedure exported under the
  #      name "main" (or similar)
  var thread = initThread(env, ProcIndex(env.procs.high),
                          hoSlice(stackStart, stackStart + stackSize),
                          @[])
  # run until an error occurrs or the main procedure finishe running
  while true:
    let res = run(env, thread, nil)
    case res.kind
    of yrkDone:
      result = res.result.intVal.int
      break
    of yrkError:
      echo "Execution failed: trap"
      result = 1
      break
    of yrkUnhandledException:
      echo "Execution failed: unhandled exception"
      break
    of yrkStubCalled, yrkUser:
      # not possible
      unreachable()
