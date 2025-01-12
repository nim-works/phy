## Implements the VM host procedures for the Phy core API.

import
  std/tables,
  vm/[
    vmalloc,
    vmenv
  ]

template trap() =
  return CallbackResult(code: cecError)

template toHost(a: VirtualAddr, size: uint64): HostPointer =
  mixin env
  var r: HostPointer
  if checkmem(env.allocator, a, size, r):
    return CallbackResult(code: cecError)
  r

template toHostChars(a: VirtualAddr, size: uint64): untyped =
  cast[ptr UncheckedArray[char]](toHost(a, size))

proc toString(x: openArray[char]): string =
  ## Creates a string from `x`. This is not the same as `$`, which would
  ## *render* `x` to text.
  if x.len > 0:
    result = newString(x.len)
    copyMem(addr result[0], addr x[0], x.len)

proc writeToFile(env: var VmEnv, file: File, data: VirtualAddr, len: int
                ): CallbackResult =
  if len < 0: trap() # guard against misuse

  let chars = toHostChars(data, len.uint64)
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
  # XXX: the current file API is meant to be temporary. It needs to be
  #      replaced with a handle-based one at some point
  hostProc "core.fileSize":
    if args[1].intVal < 0: trap() # guard against misuse
    let name = toHostChars(args[0].addrVal, args[1].intVal.uint64)
    try:
      let f = open(toString(toOpenArray(name, 0, args[1].intVal.int - 1)),
                   fmRead)
      defer: f.close()
      CallbackResult(code: cecValue, value: cast[Value](f.getFileSize()))
    except IOError:
      CallbackResult(code: cecValue, value: cast[Value](0))
  hostProc "core.readFile":
    if args[1].intVal < 0 or args[3].intVal < 0: # guard against misuse
      trap()
    let
      name = toHostChars(args[0].addrVal, args[1].intVal.uint64)
      data = toHostChars(args[2].addrVal, args[3].intVal.uint64)
    try:
      let f = open(toString(toOpenArray(name, 0, args[1].intVal.int - 1)),
                   fmRead)
      defer: f.close()
      CallbackResult(code: cecValue,
                     value: cast[Value](f.readBuffer(data, args[3].intVal)))
    except IOError:
      CallbackResult(code: cecValue, value: cast[Value](0))
