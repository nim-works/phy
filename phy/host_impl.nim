## Implements the VM host procedures for the Phy core API.

import
  system/ansi_c,
  std/[
    streams,
    tables
  ],
  vm/[
    vmalloc,
    vmenv
  ]

type
  HostEnv* = ref object of RootObj
    ## Dynamic type of the object passed to the VM callbacks.
    params*: seq[string]
      ## the program's command-line parameters
    outStream*: Stream
      ## the output stream
    errStream*: Stream
      ## the error output stream

proc c_fopen(name, mode: cstring): CFilePtr {.
  importc: "fopen", header: "<stdio.h>".}

proc c_fclose(f: CFilePtr): cint {.
  importc: "fclose", header: "<stdio.h>".}

proc c_fgetc(f: CFilePtr): cint {.
  importc: "fgetc", header: "<stdio.h>".}

proc c_ungetc(c: cint, f: CFilePtr): cint {.
  importc: "ungetc", header: "<stdio.h>".}

proc c_fseeko(f: CFilePtr, offset: csize_t, whence: cint): cint {.
  importc: "fseeko", header: "<stdio.h>".}

proc c_ftello(f: CFilePtr): int64 {.
  importc: "ftello", header: "<stdio.h>".}

proc c_fread(dst: pointer, elem: csize_t, count: csize_t, f: CFilePtr): csize_t {.
  importc: "fread", header: "<stdio.h>".}

proc c_setvbuf(f: CFilePtr, buf: pointer, mode: cint, size: csize_t): cint {.
  importc: "setvbuf", header: "<stdio.h>".}

proc c_fgets(c: cstring, n: cint, f: CFilePtr): cstring {.
  importc: "fgets", header: "<stdio.h>".}

proc c_fflush(f: CFilePtr): cint {.
  importc: "fflush", header: "<stdio.h>".}

proc c_clearerr(f: CFilePtr) {.
  importc: "clearerr", header: "<stdio.h>".}

proc c_ferror(f: CFilePtr): cint {.
  importc: "ferror", header: "<stdio.h>".}

proc strtod(buf: cstring, endptr: ptr cstring): float64 {.
  importc: "strtod", header: "<stdlib.h>".}

proc checkString(env: VmEnv, a: VirtualAddr): tuple[valid: bool, p: cstring] =
  ## Translates the guest character array pointer to a host pointer.
  ## Returns false when the character array is not fully within the guest's
  ## memory region.
  if a.uint64 == 0:
    return (true, nil) # a nil pointer is valid

  # check the characeters one by one
  var curr = a
  while true:
    var p: HostPointer
    if checkmem(env.allocator, curr, 1, p):
      # the string is partially or fully outside the guest-addressable memory
      return (false, nil)

    if p[0] == 0:
      # found the NUL terminator and it's part of the guest memory; all good
      break

    inc curr.uint64

  result = (true, cast[cstring](env.allocator.translate(a)))

template trap() =
  return CallbackResult(code: cecError)

template toHost(a: VirtualAddr, size: uint64): HostPointer =
  mixin env
  let x = a # prevent double evaluation
  var p: HostPointer = nil
  # nil address values are allowed
  if checkmem(env.allocator, x, size, p):
    return CallbackResult(code: cecError)
  p

template toHostChars(a: VirtualAddr, size: uint64): untyped =
  cast[ptr UncheckedArray[char]](toHost(a, size))

proc toString(x: openArray[char]): string =
  ## Creates a string from `x`. This is not the same as `$`, which would
  ## *render* `x` to text.
  if x.len > 0:
    result = newString(x.len)
    copyMem(addr result[0], addr x[0], x.len)

proc writeToStream(env: var VmEnv, s: Stream, data: VirtualAddr, len: int
                  ): CallbackResult =
  if len < 0: trap() # guard against misuse

  let chars = toHostChars(data, len.uint64)
  try:
    s.writeData(chars, len)
    result = CallbackResult(code: cecNothing)
  except OSError, IOError:
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

  template toHost(a: VirtualAddr, size: uint64): HostPointer =
    let x = a # prevent double evaluation
    var p: HostPointer = nil
    # nil address values are allowed
    if x != VirtualAddr(0) and checkmem(env.allocator, x, size, p):
      return CallbackResult(code: cecError)
    p

  template ret[T](val: T) =
    return CallbackResult(code: cecValue, value: cast[Value](val))

  if includeTest:
    hostProc "core.test":
      CallbackResult(code: cecValue, value: args[0])

  hostProc "core.write":
    writeToStream(env, HostEnv(cl).outStream, args[0].addrVal,
                  args[1].intVal.int)
  hostProc "core.writeErr":
    writeToStream(env, HostEnv(cl).errStream, args[0].addrVal,
                  args[1].intVal.int)
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

  # XXX: the cio host implementations are a temporary solution to make skully
  #      work. A slightly higher-level host interface that is both safer and
  #      easier to use needs to be implemented eventually, and then skully
  #      needs to intercept the high-level I/O procedures
  hostProc "cio.fopen":
    let
      fname = checkString(env, args[0].addrVal)
      mode  = checkString(env, args[1].addrVal)
    if not fname.valid or not mode.valid:
      return CallbackResult(code: cecError) # access violation
    ret c_fopen(fname.p, mode.p)
  hostProc "cio.fclose":
    ret c_fclose(cast[CFilePtr](args[0]))
  hostProc "cio.fgets":
    # fgets reads N characters from the input string, which must lie fully
    # within guest-addressable memory
    let v = c_fgets(cast[cstring](toHost(args[0].addrVal, args[1].uintVal)),
                    cast[cint](args[1].intVal),
                    cast[CFilePtr](args[2].uintVal))
    if v.isNil:
      ret 0
    else:
      # fgets returns the input pointer on success
      ret args[0]
  hostProc "cio.fgetc":
    ret c_fgetc(cast[CFilePtr](args[0].intVal))
  hostProc "cio.ungetc":
    ret c_ungetc(cast[cint](args[0].uintVal),
                 cast[CFilePtr](args[1].intVal))
  hostProc "cio.fread":
    let total = args[1].uintVal * args[2].uintVal
    # fread writes size * num bytes to where the output pointer points to
    ret c_fread(toHost(args[0].addrVal, total),
                cast[csize_t](args[1].uintVal),
                cast[csize_t](args[2].uintVal),
                cast[CFilePtr](args[3].intVal))
  hostProc "cio.fwrite":
    let total = args[1].uintVal * args[2].uintVal
    # fwrite reads size * num bytes from where the input pointer points to
    ret c_fwrite(cast[cstring](toHost(args[0].addrVal, total)),
                 cast[csize_t](args[1].uintVal),
                 cast[csize_t](args[2].uintVal),
                 cast[CFilePtr](args[3].uintVal))
  hostProc "cio.fflush":
    ret c_fflush(cast[CFilePtr](args[0]))
  hostProc "cio.fseek":
    ret c_fseeko(cast[CFilePtr](args[0].intVal),
                 cast[csize_t](args[1].uintVal),
                 cast[cint](args[2].intVal))
  hostProc "cio.ftell":
    ret c_ftello(cast[CFilePtr](args[0].intVal))
  hostProc "cio.setvbuf":
    ret c_setvbuf(cast[CFilePtr](args[0].addrVal),
                  toHost(args[1].addrVal, args[3].uintVal),
                  cast[cint](args[2].intVal),
                  cast[csize_t](args[3].uintVal))
  hostProc "cio.clearerr":
    c_clearerr(cast[CFilePtr](args[0]))
    result = CallbackResult(code: cecNothing)
  hostProc "cio.ferror":
    ret c_ferror(cast[CFilePtr](args[0]))
  hostProc "cio.getNativeStream":
    ret:
      case args[0].intVal
      of 1: stdin
      of 2: stdout
      of 3: stderr
      else: nil
  hostProc "cstr.strerror":
    # XXX: we cannot pass a cstring back into the VM
    ret 0
  hostProc "cstr.strtod":
    let tmp = checkString(env, args[0].addrVal)
    if not tmp.valid:
      return CallbackResult(code: cecError)
    ret strtod(tmp.p, nil)

  # "pe" stands for "program environment"
  hostProc "pe.paramCount":
    ret HostEnv(cl).params.len
  hostProc "pe.paramStr":
    # 1st parameter: parameter index
    # 2nd parameter: guest pointer to the destination character array (or nil)
    # 3rd parameter: number of characters in the destination array
    # returns: number of characters written. -1 signals an error
    let
      e   = HostEnv(cl)
      arg = args[0].intVal
    if arg >= 0 and arg < e.params.len:
      if args[1].uintVal == 0:
        # only return the required amount of space
        ret e.params[arg].len
      else:
        let
          dst = toHost(args[1].addrVal, args[2].uintVal)
          num = min(args[2].intVal, e.params[arg].len)
        if num > 0:
          copyMem(dst, addr e.params[arg][0], num)
        ret num
    else:
      ret -1
