## Implements the VM host procedures for the Phy core API.

import
  std/tables,
  vm/vmenv

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
