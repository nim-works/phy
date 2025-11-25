## A (somewhat) platform-agnostic implementation of the standard library's
## `os` module. Not everything is implemented yet.

proc hostParamCount(): int {.importc: "pe.paramCount".}
proc hostParamStr(i: int, str: pointer, len: int): int {.importc: "pe.paramStr".}

proc getEnv*(key: string): string =
  discard

proc paramCount*(): int =
  # hostParamCount does not include the executable's filename
  hostParamCount() + 1

proc paramStr*(i: int): string =
  if i == 0:
    # `hostParamStr` does not return the executable's filename
    result = ""
  elif i >= 1 and i < paramCount():
    let num = hostParamStr(i - 1, nil, 0)
    result = newString(num)
    discard hostParamStr(i - 1, addr result[0], num)
  else:
    # same as what the standard library does, even though it's bad form /
    # undefined behaviour to raise a defect
    raise newException(IndexDefect, formatErrorIndexBound(i, paramCount() - 1))

proc commandLineParams*(): seq[string] =
  result.newSeq(paramCount() - 1)
  for i, it in result.mpairs:
    it = paramStr(i + 1)

proc getExecArgs*(): seq[string] =
  commandLineParams()
