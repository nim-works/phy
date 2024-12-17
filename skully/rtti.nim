## Implements the creation of RTTI data. The created RTTI matches the one
## NimSkull's C code generator would produce.

import
  compiler/ast/[
    ast_types,
    ast_query,
    types
  ],
  compiler/front/[
    options
  ],
  compiler/sem/[
    sighashes
  ],
  compiler/modules/[
    modulegraphs,
    magicsys
  ],
  compiler/mir/[
    datatables,
    mirconstr,
    mirenv,
    mirtrees,
    mirtypes
  ]

proc hasRttiHeader*(env: TypeEnv, typ: TypeId): bool =
  ## Returns whether a value of `typ` has an RTTI header itself (embedded
  ## types are not considered).
  var typ = env.canonical(typ)
  if env.headerFor(typ, Lowered).kind == tkRecord:
    # seek to the root type:
    while env.headerFor(typ, Lowered).base(env) != VoidType:
      typ = env.headerFor(typ, Lowered).base(env)

    # if the first field of the root type is at position -1, the type
    # has an RTTI header
    result = env.headerFor(typ, Lowered).fieldOffset(env) == -1
  else:
    # non-record types never have an RTTI header themselves
    result = false

proc genTypeInfo2Name(t: PType): string =
  ## Copied from the NimSkully compiler.
  var res = "|"
  var it = t
  while it != nil:
    it = it.skipTypes(skipPtrs)
    if it.sym != nil:
      var m = it.sym.owner
      while m != nil and m.kind != skModule: m = m.owner
      if m == nil or sfSystemModule in m.flags:
        # produce short names for system types:
        res.add it.sym.name.s
      else:
        var p = m.owner
        if p != nil and p.kind == skPackage:
          res.add p.name.s & "."
        res.add m.name.s & "."
        res.add it.sym.name.s
    else:
      res.add $hashType(it)
    res.add "|"
    it = it[0]
  result = makeCString(res)

proc genTypeInfoV2*(env: var MirEnv, graph: ModuleGraph, typ: TypeId): DataId =
  ## Generates the ``TNimTypeV2`` data for the given type `typ` and returns
  ## the data's ID.
  let
    desc = env.types.headerFor(typ, Canonical)
    t = env.types[typ]
  assert t != nil

  let rttiType = env.types.add(graph.getCompilerProc("TNImTypeV2").typ)

  template initField(pos: int32, val: MirNode) =
    bu.subTree mnkBinding:
      bu.add MirNode(kind: mnkField, field: pos)
      bu.subTree mnkArg:
        bu.add val

  var bu = initBuilder(SourceId(0))
  # XXX: field positions are hardcoded because looking up the fields to
  #      retrieve the position is cumbersome
  bu.subTree MirNode(kind: mnkObjConstr, typ: rttiType):
    if t.kind in {tyObject, tyDistinct}:
      # name field
      initField 3:
        MirNode(kind: mnkStrLit, strVal: env.getOrIncl(genTypeInfo2Name(t)),
                typ: CstringType)

    let destroy = graph.getAttachedOp(t, attachedDestructor)
    if destroy != nil:
      # destructor field
      initField 0, MirNode(kind: mnkProcVal, prc: env.procedures.add(destroy))

    let trace = graph.getAttachedOp(t, attachedTrace)
    if trace != nil:
      # trace field:
      initField 4, MirNode(kind: mnkProcVal, prc: env.procedures.add(trace))

    if not isCyclePossible(t, graph):
      # XXX: this is not really correct, type wise. The field is of set type,
      #      but we know that it'll become an integer and thus use an int value
      #      because it's simpler
      initField 6: # flags field
        MirNode(kind: mnkIntLit, number: env.getOrIncl(1.BiggestInt),
                typ: UInt8Type)

    initField 1: # size field
      MirNode(kind: mnkIntLit, number: env.getOrIncl(desc.size(env.types)),
              typ: env.types.sizeType)

    initField 2: # align field
      MirNode(kind: mnkIntLit, number: env.getOrIncl(desc.align.BiggestInt),
              typ: env.types.sizeType)

  result = env.data.getOrPut(finish(bu)[0])
