## Implements VM modules and the procedures for linking them.
##
## Modules are not part of the core VM. In order to be able to run their code,
## all imports and host references need to be resolved first, which is achieved
## by *linking* them, producing a self-contained `VmEnv <vmenv.html#VmEnv>`_

import
  std/[options, tables],
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
    lkRelocate   ## move the procedure entry
    lkStub       ## turn into a stub entry

  LinkTable* = object
    ## Keeps track of various state that's needed for linking modules into
    ## a ``VmEnv``.
    exported: Table[string, ProcIndex]
    unresolved: Table[string, ProcIndex]
      ## not-yet-resolved entries awaiting resolution

  Action = tuple[action: LinkAction, val: uint32]

template appendAndModify(list: untyped, frm: untyped, body: untyped) =
  let start = list.len
  list.add frm
  for i {.inject.}, it {.inject.} in list.toOpenArray(start, list.high).mpairs:
    body

proc patchInstr(instr: Instr, a: int32): Instr =
  ## Returns `instr` with the 32-bit A operand replaced by `a`.
  result = Instr(instr.InstrType and not(instrAMask shl instrAShift))
  result = Instr(result.InstrType or (InstrType(a) shl instrAShift))

proc append(env: var VmEnv, tab: seq[Action], m: VmModule) =
  ## Appends all code and resources part of `m` to `env` while updating the
  ## references within.
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
      let (action, pos) = tab[it.imm32]
      if action in {lkRedirect, lkRelocate}:
        it = patchInstr(it, int32(pos))
      else:
        it = patchInstr(it, int32(it.imm32 + procOffset))

  appendAndModify env.ehTable, m.ehTable:
    it.src += codeOffset.uint32
    it.dst += codeOffset.uint32

  appendAndModify env.procs, m.procs:
    let
      entry = tab[i]
      typ = TypeId(it.typ.ord + typeOffset)
    case entry.action
    of lkImportHost:
      it = ProcHeader(kind: pkCallback, typ: typ)
      it.code.a = entry.val
    of lkKeep, lkRelocate:
      it.typ = typ
      # update the offsets
      it.code.a += codeOffset.uint32
      it.code.b += codeOffset.uint32
      it.locals.a += localsOffset.uint32
      it.locals.b += localsOffset.uint32
      if entry.action == lkRelocate:
        # move the patched-up entry to the designated destination:
        env.procs[entry.val] = move it
        it = ProcHeader(kind: pkStub, typ: it.typ)
    of lkStub, lkRedirect:
      # redirected procedures (i.e., resolved imported ones) are turned into
      # stubs, which keeps the linking simpler, as IDs don't have to be
      # shifted around
      it = ProcHeader(kind: pkStub, typ: it.typ)

proc load*(env: var VmEnv, ltab: var LinkTable, m: VmModule): bool =
  ## Loads `m` into `env`, relocating the former's resources and resolving
  ## imports where possible. If an imported procedure cannot be resolved, it
  ## stays as a stub and is registerd in `ltab` for future resolution.
  # compute the link actions
  var actions = newSeq[Action](m.procs.len)
  for i, p in m.procs.pairs:
    case p.kind
    of pkCallback:
      let name {.cursor.} = m.names[p.code.a]
      ltab.exported.withValue name, val:
        case env[val[]].kind
        of pkCallback:
          # the import imports a host procedure
          actions[i] = (lkImportHost, env[val[]].code.a)
        of pkDefault:
          # the import imports a regular bytecode procedure
          actions[i] = (lkRedirect, val[].uint32)
        of pkStub:
          unreachable("stubs shouldn't be exported")
      do:
        # make sure multiple imports of the same procedure all point to the
        # same entry in the end
        ltab.unresolved.withValue name, val:
          actions[i] = (lkRedirect, val[].uint32)
        do:
          # becomes a stub which may be resolved later
          actions[i] = (lkStub, 0'u32)
          ltab.unresolved[name] = ProcIndex(env.procs.len + i)

    of pkDefault:
      actions[i] = (lkKeep, 0'u32)
    of pkStub:
      unreachable()

  # resolve unresolved procedures using this module's exports:
  for e in m.exports.items:
    if e.kind == expProc:
      var target: ProcIndex
      if pop(ltab.unresolved, m.names[e.name], target):
        # the procedure takes over the existing stub entry, so that already
        # present code doesn't have to be patched
        actions[e.id] = (lkRelocate, target.uint32)
      else:
        target = ProcIndex(env.procs.len.uint32 + e.id)

      ltab.exported[m.names[e.name]] = target

  append(env, actions, m)

  result = true

proc load*(env: var VmEnv, ltab: var LinkTable,
           host: Table[string, VmCallback]) =
  ## Loads the given host procedures into the environment. They're
  ## automatically marked as exported.
  # XXX: this has little to do with VM modules. Move it to a separate module in
  #      the future
  for name, cb in host.pairs:
    let idx = env.callbacks.len.uint32
    env.callbacks.add cb

    # take over stub entries:
    var target: ProcIndex
    if ltab.unresolved.pop(name, target):
      env.procs[ord target] = ProcHeader(kind: pkCallback, code: idx..0'u32)
    else:
      target = env.procs.len.ProcIndex
      env.procs.add ProcHeader(kind: pkCallback, code: idx..0'u32)

    ltab.exported[name] = target

proc get*(ltab: LinkTable, name: string): Option[ProcIndex] =
  ## Returns the procedure index for the exported procedure with `name`,
  ## if present.
  if name in ltab.exported:
    some ltab.exported[name]
  else:
    none ProcIndex
