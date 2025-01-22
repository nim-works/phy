## Automatically imported into any project compiled with skully. Initializes
## the standard streams.

import system/ansi_c

proc getNativeStream(id: int): File {.importc.}

# only hooks can import foreign procedures
proc hook_getNativeStream(id: int): File {.
  compilerproc, importc: "cio.getNativeStream".}

stdin  = getNativeStream(1)
stdout = getNativeStream(2)
stderr = getNativeStream(3)

# also set the ansi_c streams
cstdin  = cast[CFilePtr](getNativeStream(1))
cstdout = cast[CFilePtr](getNativeStream(2))
cstderr = cast[CFilePtr](getNativeStream(3))
