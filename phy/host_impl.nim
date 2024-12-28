## Implements the VM host procedures for the Phy core API.

import
  system/ansi_c,
  std/tables,
  vm/[
    vmalloc,
    vmenv
  ]

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
  importc: "strtod", header: "<string.h>".}

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
    # XXX: this implementation breaks sandboxing when the cstring is not
    #      properly NUL-terminated, which is easily exploitable by adversarial
    #      code, but this is not really relevant at the moment. Hooking these
    #      low-level C procedures is a bad idea anyway...
    var tmp = strtod(cast[cstring](toHost(args[0].addrVal, 1)), nil)
    ret tmp
