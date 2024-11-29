## Implements VM modules and the procedures for linking them.
##
## Modules are not part of the core VM. In order to be able to run their code,
## all imports and host references need to be resolved first, which is achieved
## by *linking* them, producing a self-contained `VmEnv <vmenv.html#VmEnv>`_

import
  std/tables,
  vm/[vmenv, vmspec, vmtypes]

type
  VmModule* = object
    ## A module is code plus information about imports, exports, and host
    ## procedures.

    # ---- core fields
    # these fields mirror the ones from ``VmEnv``
    code*: seq[Instr]
    ehTable*: seq[EhMapping]

    locals*: seq[ValueType]
    globals*: seq[TypedValue]
    constants*: seq[TypedValue]
    procs*: seq[ProcHeader]
    types*: TypeEnv
    # ---- end of core fields

    host*: seq[string]
      ## names of host procedures. Callback procedure entries reference
      ## elements in this lsit

  HostMap = Table[string, int]
    ## maps foreign procedure names to the index of the callback implementing
    ## the procedure

template appendAndModify(list: untyped, frm: untyped, body: untyped) =
  let start = list.len
  list.add frm
  for it {.inject.} in list.toOpenArray(start, list.high).mitems:
    body

proc patchInstr(instr: Instr, a: int32): Instr =
  ## Returns `instr` with the 32-bit A operand replaced by `a`.
  result = Instr(instr.InstrType and not(instrAMask shl instrAShift))
  result = Instr(result.InstrType or (InstrType(a) shl instrAShift))

proc append(env: var VmEnv, lookup: HostMap, m: VmModule) =
  ## Appends all code and resources part of `m` to `env` while updating
  ## the references within.
  let
    codeOffset = env.code.len
    localsOffset = env.locals.len
    constOffset = env.constants.len
    globalsOffset = env.globals.len
    typeOffset = env.types.append m.types

  env.code.add m.code
  env.locals.add m.locals
  env.constants.add m.constants
  env.globals.add m.globals

  if globalsOffset > 0 and m.globals.len > 0:
    # some global references in the code might need patching
    for it in env.code.toOpenArray(codeOffset, env.code.high).mitems:
      if it.opcode == opcGetGlobal:
        it = patchInstr(it, int32(it.imm32 + globalsOffset))

  if constOffset > 0 and m.constants.len > 0:
    # some constant references in the code might need patching
    for it in env.code.toOpenArray(codeOffset, env.code.high).mitems:
      if it.opcode == opcLdConst:
        it = patchInstr(it, int32(it.imm32 + constOffset))

  if typeOffset > 0:
    # some type references in the code might need patching
    for it in env.code.toOpenArray(codeOffset, env.code.high).mitems:
      if it.opcode == opcIndCall:
        it = patchInstr(it, int32(it.imm32 + typeOffset))

  appendAndModify env.ehTable, m.ehTable:
    it.src += codeOffset.uint32
    it.dst += codeOffset.uint32

  appendAndModify env.procs, m.procs:
    it.typ = TypeId(it.typ.ord + typeOffset)
    case it.kind
    of pkCallback:
      # resolve the host procedure reference
      it.code.a = lookup[m.host[it.code.a]].uint32
    of pkDefault:
      # update the offsets
      it.code.a += codeOffset.uint32
      it.code.b += codeOffset.uint32
      it.locals.a += localsOffset.uint32
      it.locals.b += localsOffset.uint32
    of pkStub:
      discard "nothing to do"

proc link*(env: var VmEnv, host: Table[string, VmCallback],
           modules: openArray[VmModule]) =
  ## Creates a VM instance with the code from all given modules. All host
  ## procedures must be have an implementation provided by `host`.
  var lookup: HostMap
  for m in modules.items:
    # the callbacks are only added to the environment when referenced
    for it in m.host.items:
      let i = lookup.mgetOrPut(it, env.callbacks.len)
      if i == env.callbacks.len: # is it a new table entry?
        env.callbacks.add host[it]

    append(env, lookup, m)
