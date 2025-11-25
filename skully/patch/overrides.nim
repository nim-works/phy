## A special module that is automatically imported when compiling with skully.
## It provides overrides for importc'ed procedures, implemented with code that
## doesn't rely on the C standard library or C backend specific language
## features.

# the overrides need to be exportc'ed with the same name as the importc'ed
# procedure they intend to override - the code-generator/backend handle the
# rest. While simple, an unfortunate side-effect of this approach is that
# they're always part of the final executable, even if not used

{.push checks: off, profiler: off, stacktrace: off.}

proc hook_memcpy*(a, b: pointer, size: csize_t): pointer {.exportc: "memcpy".} =
  copyMem(a, b, size)

proc hook_memmove(a, b: pointer, size: csize_t): pointer {.exportc: "memmove".} =
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

proc hook_strstr(haystack, needle: cstring): cstring {.exportc: "strstr".} =
  # the most inefficient implementation imaginable
  let hLen = len(haystack)
  let nLen = len(needle)
  for i in 0 .. (hLen - nLen):
    if cmpMem(addr haystack[i], needle, nLen) == 0:
      return (addr haystack[i])

  result = nil # not found

proc hook_strcmp(a, b: cstring): int {.exportc: "strcmp".} =
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
                ): pointer {.exportc: "memchr".} =
  let arr = cast[ptr UncheckedArray[char]](cstr)
  for i in 0..<n:
    if arr[i] == c:
      return (addr arr[i])

  result = nil

proc hook_nimModInt(a, b: int, p: ptr int): bool {.exportc: "nimModInt".} =
  p[] = a mod b

proc hook_nimModInt8(a, b: int8, p: ptr int8): bool {.exportc: "nimModInt8".} =
  p[] = a mod b

proc hook_nimModInt16(a, b: int16, p: ptr int16): bool {.exportc: "nimModInt16".} =
  p[] = a mod b

proc hook_nimModInt32(a, b: int32, p: ptr int32): bool {.exportc: "nimModInt32".} =
  p[] = a mod b

proc hook_nimModInt64(a, b: int64, p: ptr int64): bool {.exportc: "nimModInt64".} =
  p[] = a mod b

proc hook_NIM_LIKELY(a: bool): bool {.exportc: "NIM_LIKELY".} =
  a

proc hook_NIM_UNLIKELY(a: bool): bool {.exportc: "NIM_UNLIKELY".} =
  a

proc hook_fabs(a: float): float {.exportc: "fabs".} =
  if a == 0.0:
    result = 0.0 # so that fabs(-0.0) == 0.0
  elif a < 0.0:
    result = -a
  else:
    result = a

proc hook_isnan(a: float): bool {.exportc: "isnan".} =
  # only works for IEEE 754 doubles
  let bits = cast[uint64](a)
  ((bits and 0x7ff0000000000000'u64) == 0x7ff0000000000000'u64) and
    (bits and 0xFFFFFFFFFFFFF'u64) != 0

# TODO: the overrides below should not be needed. Instead, the procedures
#       calling these I/O and formatting procedures need to be hooked

import std/macros

macro redir(name: untyped, proto: untyped) =
  ## Macro pragma that turns a procedure prototype into an override calling the
  ## host procedure with the given `name`.
  let orig = copyNimTree(proto)
  let s = genSym()
  let imp = copyNimTree(proto)
  imp.name = s
  imp.pragma = nnkPragma.newTree(
    nnkExprColonExpr.newTree(ident"importc", name))

  # call the actual procedure from the override:
  orig.body = nnkCall.newTree(s)
  for it in orig.params.items:
    for i in 0..<it.len-2:
      orig.body.add copyNimTree(it[i])

  orig.pragma.add ident"exportc"

  nnkStmtList.newTree(imp, orig)

proc fopen(filename, mode: cstring): File {.
  redir: "cio.fopen".}

proc fclose(f: File): cint {.
  redir: "cio.fclose".}

proc setvbuf(f: File, buf: pointer, mode: cint, size: csize_t): cint {.
  redir: "cio.setvbuf".}

proc fflush(f: File): cint {.
  redir: "cio.fflush".}

proc fread(buf: pointer, size, n: csize_t, f: File): csize_t {.
  redir: "cio.fread".}

proc fwrite(buf: pointer, size, n: csize_t, f: File): cint {.
  redir: "cio.fwrite".}

proc fgets(c: cstring, n: cint, f: File): cstring {.
  redir: "cio.fgets".}

proc fgetc(f: File): cint {.
  redir: "cio.fgetc".}

proc ungetc(c: cint, f: File): cint {.
  redir: "cio.ungetc".}

proc fseeko(f: File, offset: int64, whence: cint): cint {.
  redir: "cio.fseek".}

proc ftello(f: File): int64 {.
  redir: "cio.fseek".}

proc clearerr(f: File) {.
  redir: "cio.clearerr".}

proc ferror(f: File): cint {.
  redir: "cio.ferror".}

proc strerror(errnum: cint): cstring {.
  redir: "cstr.strerror".}

proc strtod(buf: cstring, endptr: ptr cstring): float64 {.
  redir: "cstr.strtod".}

{.pop.}
