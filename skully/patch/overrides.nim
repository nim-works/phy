## A special module that is automatically imported when compiling with skully.
## It provides overrides for importc'ed procedures, implemented with code that
## doesn't rely on the C standard library or C backend specific language
## features.
##
## All overrides are compilerprocs with a name of the form
## "hook_<original name>".

{.push checks: off, profiler: off, stacktrace: off.}

proc hook_memcpy*(a, b: pointer, size: csize_t): pointer {.compilerproc.} =
  copyMem(a, b, size)

proc hook_memmove(a, b: pointer, size: csize_t): pointer {.compilerproc.} =
  if a < b:
    var a = cast[ptr UncheckedArray[byte]](a)
    var b = cast[ptr UncheckedArray[byte]](b)
    for i in countup(0'u, size - 1):
      a[i] = b[i]
  else:
    var a = cast[ptr UncheckedArray[byte]](a)
    var b = cast[ptr UncheckedArray[byte]](b)
    for i in countdown(size - 1, 0):
      a[i] = b[i]

proc hook_strstr(haystack, needle: cstring): cstring {.compilerproc.} =
  # the most inefficient implementation imaginable
  let hLen = len(haystack)
  let nLen = len(needle)
  for i in 0 .. (hLen - nLen):
    if cmpMem(addr haystack[i], needle, nLen) == 0:
      return (addr haystack[i])

  result = nil # not found

proc hook_strcmp(a, b: cstring): int {.compilerproc.} =
  # the most inefficient implementation imaginable
  let
    aLen = len(a)
    bLen = len(b)

  if aLen < bLen:
    result = -1
  elif aLen > bLen:
    result = 1
  else:
    for i in 0..<aLen:
      result = a[i].ord - b[i].ord
      if result != 0:
        return

proc hook_memchr(cstr: pointer, c: char, n: csize_t
                ): pointer {.compilerproc.} =
  let arr = cast[ptr UncheckedArray[char]](cstr)
  for i in 0..<n:
    if arr[i] == c:
      return (addr arr[i])

  result = nil

proc hook_nimModInt(a, b: int, p: ptr int): bool {.compilerproc.} =
  p[] = a mod b

proc hook_nimModInt8(a, b: int8, p: ptr int8): bool {.compilerproc.} =
  p[] = a mod b

proc hook_nimModInt16(a, b: int16, p: ptr int16): bool {.compilerproc.} =
  p[] = a mod b

proc hook_nimModInt32(a, b: int32, p: ptr int32): bool {.compilerproc.} =
  p[] = a mod b

proc hook_nimModInt64(a, b: int64, p: ptr int64): bool {.compilerproc.} =
  p[] = a mod b

proc hook_NIM_LIKELY(a: bool): bool {.compilerproc.} =
  a

proc hook_NIM_UNLIKELY(a: bool): bool {.compilerproc.} =
  a

proc hook_fabs(a: float): float {.compilerproc.} =
  if a == 0.0:
    result = 0.0 # so that fabs(-0.0) == 0.0
  elif a < 0.0:
    result = -a
  else:
    result = a

proc hook_isnan(a: float): bool {.compilerproc.} =
  # only works for IEEE 754 doubles
  let bits = cast[uint64](a)
  ((bits and 0x7ff0000000000000'u64) == 0x7ff0000000000000'u64) and
    (bits and 0xFFFFFFFFFFFFF'u64) != 0

# TODO: the overrides below should not be needed. Instead, the procedures
#       calling these I/O and formatting procedures need to be hooked

proc hook_fopen(filename, mode: cstring): File {.
  compilerproc, importc: "cio.fopen".}

proc hook_fclose(f: File): cint {.
  compilerproc, importc: "cio.fclose".}

proc hook_setvbuf(f: File, buf: pointer, mode: cint, size: csize_t): cint {.
  compilerproc, importc: "cio.setvbuf".}

proc hook_fflush(f: File): cint {.
  compilerproc, importc: "cio.fflush".}

proc hook_fread(buf: pointer, size, n: csize_t, f: File): csize_t {.
  compilerproc, importc: "cio.fread".}

proc hook_fwrite(buf: pointer, size, n: csize_t, f: File): cint {.
  compilerproc, importc: "cio.fwrite".}

proc hook_fgets(c: cstring, n: cint, f: File): cstring {.
  compilerproc, importc: "cio.fgets".}

proc hook_fgetc(f: File): cint {.
  compilerproc, importc: "cio.fgetc".}

proc hook_ungetc(c: cint, f: File): cint {.
  compilerproc, importc: "cio.ungetc".}

proc hook_fseeko(f: File, offset: int64, whence: cint): cint {.
  compilerproc, importc: "cio.fseek".}

proc hook_ftello(f: File): int64 {.
  compilerproc, importc: "cio.fseek".}

proc hook_clearerr(f: File) {.
  compilerproc, importc: "cio.clearerr".}

proc hook_ferror(f: File): cint {.
  compilerproc, importc: "cio.ferror".}

proc hook_strerror(errnum: cint): cstring {.
  compilerproc, importc: "cstr.strerror".}

proc hook_strtod(buf: cstring, endptr: ptr cstring): float64 {.
  compilerproc, importc: "cstr.strtod".}

{.pop.}
