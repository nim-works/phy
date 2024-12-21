## Implements VM modules and the procedures for linking them.
##
## Modules are not part of the core VM. In order to be able to run their code,
## all imports and host references need to be resolved first, which is achieved
## by *linking* them, producing a self-contained `VmEnv <vmenv.html#VmEnv>`_

import
  std/tables,
  vm/[vmenv, vmspec, vmtypes]

type
  ExportKind* = enum
    expProc
    expGlobal

  Export* = object
    ## Describes an exported entity.
    kind*: ExportKind
    id*: uint32
    name*: uint32
      ## the external name under which the entity is exported. An index into
      ## the module's `names` list

  VmModule* = object
    ## A module is code plus information about imports and exports.

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

    exports*: seq[Export]
    names*: seq[string]
      ## interface names stored out-of-place

  LinkAction = enum
    lkKeep       ## keep the procedure entry
    lkRedirect   ## redirect to another entry
    lkImportHost ## turn into a host procedure entry
    lkStub       ## turn into a stub entry

  LinkTable = seq[tuple[action: LinkAction, val: uint32]]

template appendAndModify(list: untyped, frm: untyped, body: untyped) =
  let start = list.len
  list.add frm
  for i {.inject.}, it {.inject.} in list.toOpenArray(start, list.high).mpairs:
    body

proc patchInstr(instr: Instr, a: int32): Instr =
  ## Returns `instr` with the 32-bit A operand replaced by `a`.
  result = Instr(instr.InstrType and not(instrAMask shl instrAShift))
  result = Instr(result.InstrType or (InstrType(a) shl instrAShift))

proc append(env: var VmEnv, tab: LinkTable, m: VmModule) =
  ## Appends all code and resources part of `m` to `env` while updating
  ## the references within.
  let
    codeOffset = env.code.len
    localsOffset = env.locals.len
    constOffset = env.constants.len
    globalsOffset = env.globals.len
    procOffset = env.procs.len
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

  # patch all references to procedures
  for it in env.code.toOpenArray(codeOffset, env.code.high).mitems:
    # FIXME: this is ignoring procedure *values*, which are currently
    #        indistinguishable from normal integers. A new opcode for
    #        loading a procedure handle is needed
    if it.opcode == opcCall:
      let (action, pos) = tab[it.imm32 + procOffset]
      if action == lkRedirect:
        it = patchInstr(it, int32(pos))

  appendAndModify env.ehTable, m.ehTable:
    it.src += codeOffset.uint32
    it.dst += codeOffset.uint32

  appendAndModify env.procs, m.procs:
    let
      entry = tab[i + procOffset]
      typ = TypeId(it.typ.ord + typeOffset)
    case entry.action
    of lkImportHost:
      it = ProcHeader(kind: pkCallback, typ: typ)
      it.code.a = entry.val
    of lkKeep:
      it.typ = typ
      # update the offsets
      it.code.a += codeOffset.uint32
      it.code.b += codeOffset.uint32
      it.locals.a += localsOffset.uint32
      it.locals.b += localsOffset.uint32
    of lkStub, lkRedirect:
      # redirected procedures (i.e., resolved imported ones) are turned into
      # stubs, which keeps the linking simpler, as IDs don't have to be
      # shifted around
      it = ProcHeader(kind: pkStub, typ: it.typ)

proc link*(env: var VmEnv, host: Table[string, VmCallback],
           modules: openArray[VmModule]) =
  ## Creates a VM instance with the code from all given modules. If an imported
  ## procedure resolves to neither a regular procedure nor host procedure
  ## provided by `host`, it stays as a stub.
  var
    lookup: Table[string, int]
      ## keeps track of the already registered callbacks. Callbacks are only
      ## added to the environment when actually referenced
    exported: Table[string, uint32]
    tab: LinkTable

  # first pass: collect the IDs corresponding to interface names
  block:
    var offset = 0'u32
    for m in modules.items:
      for e in m.exports.items:
        if e.kind == expProc:
          # if there exists more than one export with the same interface name,
          # the last one prevails
          exported[m.names[e.name]] = offset + e.id

      offset += m.procs.len.uint32

    tab.newSeq(offset)

  var i = 0
  # second pass: compute the link action for each procedure
  for m in modules.items:
    for p in m.procs.items:
      if p.kind == pkCallback:
        let name {.cursor.} = m.names[p.code.a]
        if name in exported:
          # the import imports a regular procedure
          tab[i] = (lkRedirect, exported[name])
        elif name in host:
          # the import imports a host procedure
          let i = lookup.mgetOrPut(name, env.callbacks.len)
          if i == env.callbacks.len: # is it a new table entry?
            env.callbacks.add host[name]

          tab[i] = (lkImportHost, i.uint32)
        else:
          # the import cannot be resolved, turn the procedure entry into
          # a stub
          tab[i] = (lkStub, 0'u32)
      else:
        tab[i] = (lkKeep, 0'u32)

      inc i

  reset lookup # free the memory already, it's not needed anymore

  for m in modules.items:
    append(env, tab, m)
