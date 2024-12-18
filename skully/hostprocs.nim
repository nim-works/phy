## Provides the VM callback implementations for the various foreign procedures
## used by skully-compiled programs.

import
  std/tables,
  system/ansi_c,
  vm/[vmalloc, vmenv]

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

proc hostProcedures*(): Table[string, VmCallback] =
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

  hostProc "cio.fgets":
    # fgets reads N characters from the input address. This memory must be
    # accessible by the VM
    let v = c_fgets(cast[cstring](toHost(args[0].addrVal, args[1].uintVal)),
                    cast[cint](args[1].intVal),
                    cast[CFilePtr](args[2].uintVal))
    if v.isNil:
      result = CallbackResult(code: cecValue, value: cast[Value](0))
    else:
      # fgets returns the input pointer on success
      result = CallbackResult(code: cecValue, value: args[0])
  hostProc "cio.fwrite":
    let total = args[1].uintVal * args[2].uintVal
    # fwrite reads size * num bytes from where the input pointer points to
    ret c_fwrite(cast[cstring](toHost(args[0].addrVal, total)),
                 cast[csize_t](args[1].uintVal),
                 cast[csize_t](args[2].uintVal),
                 cast[CFilePtr](args[3].uintVal))
  hostProc "cio.fflush":
    ret c_fflush(cast[CFilePtr](args[0]))
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
    #      low-level C procedure is a bad idea anyway...
    var tmp = strtod(cast[cstring](toHost(args[0].addrVal, 1)), nil)
    ret tmp
