## Implements the VM host procedures for the Phy core API.

import
  std/tables,
  vm/[
    vmalloc,
    vmenv
  ]

template trap() =
  return CallbackResult(code: cecError)

proc writeToFile(env: var VmEnv, file: File, data: VirtualAddr, len: int
                ): CallbackResult =
  if len < 0: trap() # guard against misuse

  var p: HostPointer
  if checkmem(env.allocator, data, len.uint64, p):
    return CallbackResult(code: cecError)

  let chars = cast[ptr UncheckedArray[char]](p)
  try:
    discard stdout.writeChars(toOpenArray(chars, 0, len - 1), 0, len)
    result = CallbackResult(code: cecNothing)
  except IOError:
    # TODO: I/O errors need to be turned into either exceptions (very hard) or
    #       error codes that the callsite then turns into exception (or
    #       something else; easy). Trapping is a temporary solution to at
    #       least not ignore the error
    trap()

proc hostProcedures*(includeTest: bool): Table[string, VmCallback] =
  ## If `includeTest` is true, some host procedures only meant for testing are
  ## included.
  template hostProc(name: string, body: untyped) {.dirty.} =
    result[name] = proc(env: var VmEnv, args: openArray[Value],
                        cl: RootRef): CallbackResult {.nimcall, raises: [].} =
      body

  if includeTest:
    hostProc "core.test":
      CallbackResult(code: cecValue, value: args[0])

  # TODO: the streams to write to need to be configurable from
  #       the outside, through the ref object passed to the callbacks
  hostProc "core.write":
    writeToFile(env, stdout, args[0].addrVal, args[1].intVal.int)
  hostProc "core.writeErr":
    writeToFile(env, stderr, args[0].addrVal, args[1].intVal.int)
