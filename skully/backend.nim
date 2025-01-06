## Implements the code generator for Skully. It's integrated into the
## compilation process like the NimSkull-native code generators are, via the
## ``backends`` module.

import
  std/[
    importutils,
    packedsets,
    strtabs,
    tables
  ],
  compiler/front/[
    options,
    msgs
  ],
  compiler/sem/[
    modulelowering
  ],
  compiler/ast/[
    ast,
    ast_types,
    ast_query,
    idents,
    lineinfos,
    report_enums,
    reports_sem,
    types
  ],
  compiler/modules/[
    modulegraphs,
    magicsys
  ],
  compiler/utils/[
    bitsets,
    containers,
    platform
  ],
  compiler/backend/[
    backends
  ],
  compiler/mir/[
    datatables,
    mirenv,
    mirgen,
    mirtrees,
    mirtypes,
    sourcemaps
  ],
  passes/[
    builders,
    spec,
    trees
  ],
  skully/[
    rtti
  ]

from compiler/mir/mirbodies import MirBody, `[]`

import vm/utils as vm_utils
import skully/passes as phy_passes

type
  Node = TreeNode[NodeKind]

  ProcContext = object
    localMap: Table[LocalId, uint32]
    labelMap: Table[LabelId, uint32]
    params: seq[uint32]
    indirectLocals: PackedSet[LocalId]
      ## all locals that are references and not locals with storage
    nextLabel: uint32
    nextLocal: uint32
    temps: seq[TypeId]
    active: bool

    sources: SourceMap

  Context = object
    graph: ModuleGraph
    lit: Literals

    typeCache: Table[TypeId, uint32]
      ## cache for the IL types resulting from MIR types
    types: OrderedTable[seq[Node], uint32]
      ## maps IL types to the associated ID (i.e., position in the typedefs
      ## tree). This is used for simple culling of structurally equal types
      ## XXX: this is incredibly inefficient. Not only does it allocate a lot
      ##      of small sequences, the ordered table also incurs additional
      ##      overhead. A table that allows storing the actual key data (i.e.,
      ##      the type tree, in this case) should be used instead

    rttiCache: Table[TypeId, uint32]
      ## caches the RTTIv2 globals created for types

    procMap: Table[ProcedureId, uint32]
      ## maps MIR procedure IDs to their corresponding IL procedure IDs. The
      ## MIR procedure IDs cannot be used directly as IL procedure ID because
      ## the partial procedure handling creates IL procedure that have no MIR
      ## counterpart
    nextProc: uint32
      ## the ID to use for the next registered procedure

    globalsMap: Table[GlobalId, uint32]
      ## maps MIR globals and constants to IL globals
    constMap: Table[ConstId, uint32]
    dataMap: Table[DataId, uint32]
    globals: seq[tuple[typ: TypeId, address: uint32]]
      ## the IL globals. address is the virtual address the underlying storage
      ## is located at
    globalsAddress: uint32
      ## the lower bound for virtual addresses of new global variable storage

    prc: ProcContext

  Expr = object
    nodes: seq[Node]
    typ {.requiresInit.}: TypeId

  ProcMap = SeqMap[uint32, seq[Node]]

const
  MagicsToKeep = {mNewSeq, mSetLengthSeq, mAppendSeqElem,
                  mEnumToStr, mDotDot, mEqCString, mAbsI}
  StrLitFlag = 1'i64 shl 62
    ## or'ed into the capacity of seqs and strings in order to mark the
    ## data as being immutable
  AddressBias = 4096
    ## must be added to all raw address values, in order to undo the
    ## offset applied to address value on memory access performed by the VM
  StackSize = 1024 * 1024 # 1 MiB

using
  bu: var Builder[NodeKind]
  tree: MirTree
  n: NodePosition
  stmts: var Builder[NodeKind]
  env: MirEnv
  c: var Context

proc genType(c; env: TypeEnv, typ: TypeId): uint32
proc genProcType(c; env: MirEnv, typ: TypeId, ignoreClosure = false): Node
proc gen(c; env: MirEnv, tree; n; wantsValue: bool): Expr

func align[T](val, to: T): T =
  ## `to` must be a power-of-two.
  let mask = to - 1
  result = (val + mask) and not mask

proc warn(c; src: SourceId, msg: string) =
  # the warning is not a user-provided one, but there's no other warning report
  # kind that fits, nor is it possible to introduce one without forking the
  # compiler
  c.graph.config.localReport(c.prc.sources[src],
    SemReport(kind: rsemUserWarning, str: msg))

func payloadType(env: TypeEnv, typ: TypeId): TypeId =
  ## Returns the ID of a seq/string type's payload type.
  env.headerFor(env[env.lookupField(typ, 1)].typ, Canonical).elem()

func isPassByRef(env: TypeEnv; typ: TypeId, param: int): bool =
  # XXX: the MIR type API doesn't support querying the a proc type
  #      parameter by position...
  for (i, _, flags) in env.params(env.headerFor(typ, Canonical)):
    if i == param:
      return pfByRef in flags
  unreachable()

iterator items(tree: MirTree, n: NodePosition, start: int,
               last: BackwardsIndex): NodePosition =
  var it = tree.child(n, start)
  for _ in start .. (tree.len(n) - ord(last)):
    yield it
    it = tree.sibling(it)

template node(k: NodeKind, v: uint32): Node =
  Node(kind: k, val: v)

proc makeExpr(nodes: sink seq[Node], typ: TypeId): Expr {.inline.} =
  Expr(nodes: nodes, typ: typ)

template buildExpr(typ: TypeId, body: untyped): Expr =
  if true:
    let t = typ
    var bu {.inject.} = initBuilder[NodeKind]()
    body
    makeExpr(finish(bu), t)
  else:
    unreachable()

proc goto(bu; label: uint32) =
  bu.subTree Goto:
    bu.add node(Immediate, label)

proc join(bu; label: uint32) =
  bu.subTree Join:
    bu.add node(Immediate, label)

proc takeAddr(e: Expr, bu) =
  if e.nodes[0].kind == Deref:
    # drop the `Deref`
    bu.add e.nodes.toOpenArray(2, e.nodes.high)
  else:
    bu.subTree Addr:
      bu.add e.nodes

proc use(bu; e: Expr) =
  case e.nodes[0].kind
  of Local, At, Field:
    bu.subTree Copy:
      bu.add e.nodes
  of Deref:
    # turn the ``Deref`` into a ``Load``
    bu.subTree Load:
      bu.add e.nodes[1]
      bu.add e.nodes.toOpenArray(2, e.nodes.high)
  else:
    bu.add e.nodes

proc useLvalue(bu; e: Expr) =
  bu.add e.nodes

proc genAsgn(dest: Expr, src: Expr; bu) =
  if dest.nodes.len == 0:
    bu.subTree Drop:
      bu.use src
  elif dest.nodes[0].kind == Deref:
    bu.subTree NodeKind.Store:
      bu.add dest.nodes[1]
      bu.add dest.nodes.toOpenArray(2, dest.nodes.high)
      bu.use src
  else:
    assert dest.nodes[0].kind != Load
    bu.subTree Asgn:
      bu.useLvalue dest
      bu.use src

template addStmt(sub: var Builder[NodeKind], kind: NodeKind, body: untyped) =
  if true:
    var bu {.inject.} = initBuilder[NodeKind](kind)
    body
    sub.add finish(bu)

template putInto(builder: Builder[NodeKind], dest: Expr, kind: NodeKind,
                 body: untyped) =
  if true:
    var bu {.inject.} = initBuilder(kind)
    body
    genAsgn(dest, makeExpr(bu.finish(), dest.typ), builder)

proc putInto(bu; dest: Expr, node: Node) =
  genAsgn(dest, makeExpr(@[node], dest.typ), bu)

template makeExpr(typ: TypeId, body: untyped): Expr =
  if true:
    let t = typ
    var bu {.inject.} = initBuilder[NodeKind]()
    body
    makeExpr(bu.finish(), t)
  else:
    unreachable()

proc registerProc(c; prc: ProcedureId): uint32 =
  result = c.procMap.mgetOrPut(prc, c.nextProc)
  if result == c.nextProc: # is it a not-yet-seen procedure?
    inc c.nextProc

proc compilerProc(c; env: var MirEnv, name: string): Node =
  ## Returns a ``Proc`` reference to the compilerproc with the given `name`.
  ## The compilerproc is added to `c` and `env` first, if it hasn't been
  ## already.
  let p = c.graph.getCompilerProc(name)
  result = node(Proc, c.registerProc(env.procedures.add(p)))

proc typeRef(c; env: TypeEnv, typ: TypeId): Node =
  node(Type, c.genType(env, typ))

proc typeRef(c; env: MirEnv, typ: TypeId): Node =
  typeRef(c, env.types, typ)

proc genFlexArrayType(c; env: TypeEnv; typ: TypeId): uint32 =
  ## Returns the IL type ID of an array type with unknown length.
  var bu = initBuilder[NodeKind](Array)
  # size and number of elements don't matter, but use the lowest possible
  # value to be safe
  bu.add node(Immediate, 1) # size
  bu.add node(Immediate, 0) # alignment
  bu.add node(Immediate, 0) # elements
  bu.add typeRef(c, env, typ)
  result = c.types.mgetOrPut(finish(bu), c.types.len.uint32)

proc translateProcType(c; env: TypeEnv, id: TypeId, ignoreClosure: bool, bu) =
  let desc = env.headerFor(id, Canonical)
  bu.subTree ProcTy:
    if desc.retType(env) == VoidType:
      bu.subTree Void: discard
    else:
      bu.add typeRef(c, env, desc.retType(env))

    for (i, typ, flags) in env.params(desc):
      # exclude compile-time-only parameters
      if env.canonical(typ) != VoidType:
        if pfByRef in flags:
          bu.add typeRef(c, env, PointerType)
        else:
          bu.add typeRef(c, env, typ)

    if desc.callConv(env) == ccClosure and not ignoreClosure:
      bu.add typeRef(c, env, PointerType)

proc embedTaggedUnion(c; env: TypeEnv, id: TypeId, bu) =
  privateAccess(RecField) # required for accessing the field offsets

  proc addType(c; bu: sink Builder[NodeKind]): uint32 =
    c.types.mgetOrPut(finish(bu), c.types.len.uint32)

  let
    desc = env.headerFor(id, Lowered)
    tagField = env.lookupField(id, 0)

  # compute the alignment for the union:
  # TODO: this needs to be upstreamed into NimSkull
  var alignment = 0'i16
  for _, it in env.fields(desc, 1):
    let sub = env.headerFor(it.typ, Canonical)
    if env.isEmbedded(it.typ):
      # an anonymous record; its fields need to be considered too
      for _, inner in env.fields(sub):
        alignment = max(alignment, env.headerFor(inner.typ, Canonical).align)
    else:
      alignment = max(alignment, sub.align)

  let offset = align(env[tagField].offset.uint32 + desc.size(env).uint32,
                     uint32 alignment)
    ## the offset of the union within the embedding record

  let inner = block:
    # XXX: size and alignment are currently ignored, as it's simpler this way
    #      and no pass inspects these values anyhow (at least at the time of
    #      writing)
    var bu = initBuilder(Union)
    bu.add node(Immediate, 0)
    bu.add node(Immediate, uint32 alignment)
    for _, it in env.fields(desc, 1):
      if env.isEmbedded(it.typ):
        if env.headerFor(it.typ, Lowered).numFields == 0:
          # IL record types must not be empty; add a dummy field
          bu.add node(UInt, 1)
        else:
          # emit the record type for the embedded type, but make sure to
          # correct the field offsets; they need to be relative to the start
          # of the union, not to the start of the embedding record
          var bu2 = initBuilder(Record)
          bu2.add node(Immediate, 0)
          bu2.add node(Immediate, 0)
          for _, recf in env.fields(env.headerFor(it.typ, Lowered)):
            bu2.subTree Field:
              bu2.add node(Immediate, recf.offset.uint32 - offset)
              bu2.add typeRef(c, env, recf.typ)

          bu.add node(Type, c.addType(bu2))
      else:
        bu.add typeRef(c, env, it.typ)

    c.addType(bu) # the union type

  # emit the necessary fields for the embedding record. The tag field is
  # inlined into the embedder, which gets around having to use another
  # wrapper type
  bu.subTree Field:
    bu.add node(Immediate, env[tagField].offset.uint32)
    bu.add typeRef(c, env, env[tagField].typ)

  bu.subTree Field:
    bu.add node(Immediate, offset)
    bu.add node(Type, inner)

proc translate(c; env: TypeEnv, id: TypeId, bu) =
  let desc = env.headerFor(id, Lowered)
  case desc.kind
  of tkInt:
    bu.add node(Int, desc.size(env).uint32)
  of tkFloat:
    bu.add node(Float, desc.size(env).uint32)
  of tkUInt:
    bu.add node(UInt, desc.size(env).uint32)
  of tkPointer:
    bu.add node(UInt, desc.size(env).uint32)
  of tkBool, tkChar:
    bu.add node(UInt, 1)
  of tkArray:
    bu.subTree Array:
      bu.add node(Immediate, desc.size(env).uint32)
      bu.add node(Immediate, desc.align.uint32)
      bu.add node(Immediate, desc.arrayLen(env).uint32)
      bu.add typeRef(c, env, desc.elem())
  of tkUncheckedArray:
    bu.subTree Array:
      bu.add node(Immediate, 0)
      bu.add node(Immediate, desc.align.uint32)
      bu.add node(Immediate, 1)
      bu.add typeRef(c, env, desc.elem())
  of tkRecord:
    let (size, alignment) =
      if desc.size(env) >= 0:
        (desc.size(env).int, desc.align.int)
      elif env[id] != nil and
           env[id].skipTypes(abstractVar).kind == tyOpenArray:
        # the size for openArrays is never filled in correctly; we have to
        # manually correct it here
        (c.graph.config.target.ptrSize * 2, c.graph.config.target.ptrSize)
      else:
        (szUnknownSize, szUnknownSize)

    assert size >= 0
    bu.subTree Record:
      bu.add node(Immediate, size.uint32)
      bu.add node(Immediate, alignment.uint32)

      if desc.kind == tkRecord and desc.base(env) != VoidType:
        # the inherited-from type is added as the first field
        bu.subTree Field:
          bu.add node(Immediate, 0)
          bu.add typeRef(c, env, desc.base(env))

      for f, recf in env.fields(desc):
        privateAccess(RecField)
        if env.headerFor(recf.typ, Canonical).kind == tkTaggedUnion:
          c.embedTaggedUnion(env, recf.typ, bu)
        else:
          bu.subTree Field:
            bu.add node(Immediate, recf.offset.uint32)
            bu.add typeRef(c, env, recf.typ)
  of tkUnion:
    bu.subTree Union:
      bu.add node(Immediate, desc.size(env).uint32)
      bu.add node(Immediate, desc.align.uint32)
      for _, recf in env.fields(desc):
        bu.add typeRef(c, env, recf.typ)
  of tkImported:
    # treat imported types as if they were equivalent to their "underlying"
    # type
    # XXX: in the longer term, and once the ILs are extended sufficiently, an
    #      "imported" type needs to be translated to the appropriate foreign
    #      type
    translate(c, env, elem(desc), bu)
  of tkProc, tkPtr, tkRef, tkVar, tkLent, tkCstring:
    c.translate(env, PointerType, bu)
  else:
    unreachable($desc.kind)

proc genProcType(c; env: MirEnv, typ: TypeId, ignoreClosure = false): Node =
  let typ = env.types.canonical(typ)
  assert env.types.headerFor(typ, Canonical).kind in {tkProc, tkClosure}

  # XXX: the type is currently not cached
  var bu = initBuilder[NodeKind]()
  c.translateProcType(env.types, typ, ignoreClosure, bu)
  node(Type, c.types.mgetOrPut(finish(bu), c.types.len.uint32))

proc genType(c; env: TypeEnv, typ: TypeId): uint32 =
  let typ = env.canonical(typ)
  c.typeCache.withValue typ, val:
    # already cached
    result = val[]
  do:
    # translate the type and cache it
    var bu = initBuilder[NodeKind]()
    c.translate(env, typ, bu)
    result = c.types.mgetOrPut(finish(bu), c.types.len.uint32)
    c.typeCache[typ] = result

proc genField(c; env: MirEnv; e: Expr; pos: int32, bu) =
  ## Emits a field access for field `pos`.
  let typ = env.types.canonical(e.typ)

  proc findType(env: TypeEnv, typ: TypeId, pos: int32): (TypeId, int) =
    let desc = env.headerFor(typ, Lowered)
    if desc.fieldOffset(env) > pos:
      result = findType(env, desc.base(env), pos)
      result[1] += 1
    else:
      result = (typ, 0)

  proc findField(env: TypeEnv, typ: TypeId, id: FieldId,
                 steps: var seq[uint32]): bool =
    let desc = env.headerFor(typ, Lowered)
    var pos = 0
    block search:
      for (f, recf) in env.fields(desc):
        if env.headerFor(recf.typ, Canonical).kind == tkTaggedUnion:
          # a tagged union field counts as two: one for the tag and one for
          # the union
          inc pos # skip the tag
          if findField(env, recf.typ, id, steps):
            if steps[^1] == 0: # is the field a tag field?
              # the tag is part of the embedder
              steps.del(steps.high)
              dec pos
            else:
              dec steps[^1]
            break search
        elif env[recf.typ].isNil and
             env.headerFor(recf.typ, Canonical).kind == tkRecord:
          # it's an embedded record type
          if findField(env, recf.typ, id, steps):
            break search
        elif f == id:
          break search

        inc pos

      # not found
      return false

    if desc.kind == tkRecord and desc.base(env) != VoidType:
      # account for the base field (which is located at the start of the
      # record)
      inc pos

    result = true
    steps.add uint32(pos)

  case env.types.headerFor(typ, Lowered).kind
  of tkRecord:
    let
      id = env.types.lookupField(typ, pos)
      (typ, depth) = findType(env.types, typ, pos)
    var steps: seq[uint32]
    doAssert findField(env.types, typ, id, steps)
    # a MIR field access doesn't translate to a single IL field access
    # because:
    # 1. parent type access is explicit in the Il
    # 2. tagged unions are standalone records in the IL

    var nodes: seq[Node]
    for _ in 0..<(steps.len + depth):
      nodes.add node(Field, 2)

    nodes.add e.nodes

    # add the base field access first...
    for _ in 0..<depth:
      nodes.add node(Immediate, 0)

    # ... then the extra steps, but in reverse
    for i in countdown(steps.high, 0):
      nodes.add node(Immediate, uint32 steps[i])

    bu.add nodes
  of tkUnion:
    bu.subTree Field:
      bu.add e.nodes
      bu.add node(Immediate, uint32 pos)
  else:
    unreachable()

proc genConst(c; env; tree; n; dest: Expr, stmts) =
  ## Emits the construction logic for the MIR constant expression `n`.
  template putIntoDest(n: Node) =
    stmts.putInto dest, n

  iterator args(tree; n): (int, NodePosition) =
    var i = 0
    for it in tree.items(n, 0, ^1):
      yield (i, tree.last(it))
      inc i

  let typ = env.types.canonical(tree[n].typ)

  case tree[n].kind
  of mnkIntLit, mnkUIntLit:
    putIntoDest node(IntVal, c.lit.pack(env.getInt(tree[n].number)))
  of mnkFloatLit:
    putIntoDest node(FloatVal, c.lit.pack(env.getFloat(tree[n].number)))
  of mnkProcVal:
    putIntoDest node(ProcVal, c.registerProc(tree[n].prc))
  of mnkArrayConstr:
    for i, it in tree.args(n):
      let nDest = makeExpr tree[it].typ:
        bu.subTree At:
          bu.useLvalue dest
          bu.add node(IntVal, c.lit.pack(i))
      c.genConst(env, tree, it, nDest, stmts)
  of mnkTupleConstr, mnkClosureConstr:
    for i, it in tree.args(n):
      let nDest = makeExpr tree[it].typ:
        bu.subTree Field:
          bu.useLvalue dest
          bu.add node(Immediate, i.uint32)
      c.genConst(env, tree, it, nDest, stmts)
  of mnkObjConstr:
    for it in tree.subNodes(n):
      let val = tree.last(tree.child(it, 1))
      let nDest = makeExpr tree[val].typ:
        c.genField(env, dest, tree[it, 0].field, bu)
      c.genConst(env, tree, val, nDest, stmts)
  of mnkStrLit:
    let str {.cursor.} = env[tree[n].strVal]

    proc emitString(c; str: string, data: uint32, stmts) {.nimcall.} =
      # there's no built-in support for strings in the ILs/VM, requiring
      # the manual initialization of each character
      for i, it in pairs(str):
        stmts.addStmt NodeKind.Store:
          bu.add node(UInt, 1)
          bu.add node(IntVal, c.lit.pack(int64(data) + i))
          bu.add node(IntVal, c.lit.pack(ord it))

      # emit the NUL terminator:
      stmts.addStmt NodeKind.Store:
        bu.add node(UInt, 1)
        bu.add node(IntVal, c.lit.pack(int64(data) + str.len))
        bu.add node(IntVal, c.lit.pack(0))

    case env.types.headerFor(typ, Canonical).kind
    of tkCstring:
      # a cstring is a pointer to a raw character sequence followed by a NUL
      # terminator
      let data = c.globalsAddress + AddressBias
      c.globalsAddress += str.len.uint32 + 1
      c.emitString(str, data, stmts)

      putIntoDest node(IntVal, c.lit.pack(data.int64))
    of tkString:
      # it's a NimSkull string (a length + payload pointer)
      let
        intSize = c.graph.config.target.intSize.uint32
        start   = align(c.globalsAddress, intSize)
        data    = start + AddressBias
      c.globalsAddress = start + intSize + str.len.uint32 + 1 # reserve space

      # emit the capacity initialization:
      stmts.addStmt NodeKind.Store:
        bu.add typeRef(c, env, env.types.sizeType)
        bu.add node(IntVal, c.lit.pack(data.int64))
        bu.add node(IntVal, c.lit.pack(str.len or StrLitFlag))

      c.emitString(str, data + 8, stmts)

      stmts.addStmt Asgn:
        bu.subTree Field:
          bu.useLvalue dest
          bu.add node(Immediate, 0)
        bu.add node(IntVal, c.lit.pack(str.len))
      stmts.addStmt Asgn:
        bu.subTree Field:
          bu.useLvalue dest
          bu.add node(Immediate, 1)
        bu.add node(IntVal, c.lit.pack(data.int64))
    else:
      unreachable()
  of mnkSeqConstr:
    let
      intSize = c.graph.config.target.intSize.uint32
      elem = env.types.headerFor(typ, Canonical).elem
      size = env.types.headerFor(elem, Canonical).size(env.types)
      alignment = env.types.headerFor(elem, Canonical).align.uint32

    # the payload address must satisfy the alignment requirements of the
    # element type
    let
      payload     = align(c.globalsAddress, alignment)
      data        = align(payload + intSize, alignment)
      payloadAddr = payload + AddressBias
      dataAddr    = data + AddressBias
    # reserve enough space for the whole payload:
    c.globalsAddress = data + uint32(size * tree.len(n))

    # emit the seq construction:
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 0)
      bu.add node(IntVal, c.lit.pack(tree.len(n)))

    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 1)
      bu.add node(IntVal, c.lit.pack(payloadAddr.int64))

    # emit the capacity initialization:
    stmts.addStmt NodeKind.Store:
      bu.add typeRef(c, env, env.types.sizeType)
      bu.add node(IntVal, c.lit.pack(payloadAddr.int64))
      bu.add node(IntVal, c.lit.pack(tree.len(n) or StrLitFlag))

    # emit the payload data initialization:
    for i, it in tree.args(n):
      let nDest = makeExpr elem:
        bu.subTree Deref:
          bu.add typeRef(c, env, elem)
          bu.add node(IntVal, c.lit.pack(dataAddr.int64 + size * i))

      c.genConst(env, tree, it, nDest, stmts)
  of mnkSetConstr:
    let desc = env.types.headerFor(typ, Lowered)

    # evaluate the constant set first:
    var bitset: TBitSet
    bitset.bitSetInit(desc.size(env.types).int)

    for it in tree.items(n, 0, ^1):
      if tree[it].kind == mnkRange:
        bitSetInclRange(bitset,
          env.getInt(tree[it, 0].number) .. env.getInt(tree[it, 1].number))
      else:
        bitSetIncl(bitset, env.getInt(tree[it].number))

    if bitset.len > 8:
      # the set is implemented as an array
      for i, it in bitset.pairs:
        # globals are zero-initialized by default, and therefore zero
        # assignments can be omitted
        if it != 0:
          stmts.addStmt Asgn:
            bu.subTree At:
              bu.useLvalue dest
              bu.add node(IntVal, c.lit.pack(i))
            bu.add node(IntVal, c.lit.pack(it.int))
    else:
      # the set fits into an integer
      var value = 0'i64
      for i, it in bitset.pairs:
        value = value or (int64(it) shl (i * 8))
      putIntoDest node(IntVal, c.lit.pack(value))
  else:
    unreachable()

proc newGlobal(c; env: MirEnv, typ: TypeId): uint32 =
  let desc = env.types.headerFor(typ, Lowered)
  # align the address first:
  c.globalsAddress = align(c.globalsAddress, desc.align.uint32)
  c.globals.add (typ, c.globalsAddress)
  # occupy the memory slot:
  c.globalsAddress += desc.size(env.types).uint32

  result = c.globals.high.uint32

proc newLabel(c: var ProcContext): uint32 =
  result = c.nextLabel
  inc c.nextLabel

proc newTemp(c; typ: TypeId): Expr =
  assert typ != VoidType
  let id = c.prc.nextLocal + c.prc.temps.len.uint32
  c.prc.temps.add typ
  result = makeExpr(@[node(Local, id)], typ)

proc request(c: var ProcContext; label: LabelId): uint32 =
  if label in c.labelMap:
    result = c.labelMap[label]
  else:
    result = c.newLabel()
    c.labelMap[label] = result

proc genExit(c; tree; n; bu) =
  case tree[n].kind
  of mnkResume:
    bu.subTree Unwind:
      discard
  of mnkLabel:
    bu.subTree Goto:
      bu.add node(Immediate, c.prc.request(tree[n].label))
  else:
    unreachable()

proc translateValue(c; env: MirEnv, tree: MirTree, n: NodePosition,
                    wantValue: bool, bu) =
  ## `wantValue` tells translation an rvalue expression is expected.
  template recurse(n: NodePosition, wantValue: bool) =
    c.translateValue(env, tree, n, wantValue, bu)

  template wrapCopy(body: untyped) =
    if wantValue:
      bu.subTree Copy: body
    else:
      body

  template wrapCopy(kind: NodeKind, body: untyped) =
    wrapCopy:
      bu.subTree kind:
        body

  case tree[n].kind
  of mnkGlobal:
    # all globals are pointers (because the target IL doesn't support mutable
    # global variables)
    bu.subTree (if wantValue: Load else: Deref):
      bu.add typeRef(c, env, tree[n].typ)
      bu.subTree Copy:
        bu.add node(Global, c.globalsMap[tree[n].global])
  of mnkNilLit:
    bu.add node(IntVal, 0)
  of mnkIntLit, mnkUIntLit:
    bu.add node(IntVal, c.lit.pack(env.getInt(tree[n].number)))
  of mnkFloatLit:
    bu.add node(FloatVal, c.lit.pack(env.getFloat(tree[n].number)))
  of mnkTemp, mnkLocal:
    # MIR temporaries and locals can never be references
    wrapCopy:
      bu.add node(Local, c.prc.localMap[tree[n].local])
  of mnkParam:
    if tree[n].local in c.prc.indirectLocals:
      # needs a pointer indirection
      bu.subTree (if wantValue: Load else: Deref):
        bu.add typeRef(c, env, tree[n].typ)
        bu.subTree Copy:
          bu.add node(Local, c.prc.localMap[tree[n].local])
    else:
      wrapCopy:
        bu.add node(Local, c.prc.localMap[tree[n].local])
  of mnkAlias:
    # aliases are implemented as pointers
    bu.subTree (if wantValue: Load else: Deref):
      bu.add typeRef(c, env, tree[n].typ)
      bu.subTree Copy:
        bu.add node(Local, c.prc.localMap[tree[n].local])
  of mnkConst:
    let id = tree[n].cnst
    if isAnon(id):
      # TODO: inline small anonymous constants (e.g., small sets)
      if extract(id) notin c.dataMap:
        c.dataMap[extract(id)] = c.newGlobal(env, tree[n].typ)

      bu.subTree (if wantValue: Load else: Deref):
        bu.add typeRef(c, env, tree[n].typ)
        bu.subTree Copy:
          bu.add node(Global, c.dataMap[extract(id)])
    else:
      bu.subTree (if wantValue: Load else: Deref):
        bu.add typeRef(c, env, tree[n].typ)
        bu.subTree Copy:
          bu.add node(Global, c.constMap[tree[n].cnst])
  of mnkProcVal:
    bu.add node(ProcVal, c.registerProc(tree[n].prc))
  of mnkDeref, mnkDerefView:
    bu.subTree (if wantValue: Load else: Deref):
      bu.add typeRef(c, env, tree[n].typ)
      recurse(tree.child(n, 0), true)
  of mnkPathPos:
    wrapCopy Field:
      recurse(tree.child(n, 0), false)
      bu.add node(Immediate, tree[n, 1].imm)
  of mnkPathNamed:
    let e = c.gen(env, tree, tree.child(n, 0), false)
    wrapCopy:
      c.genField(env, e, tree[n, 1].field, bu)
  of mnkPathVariant:
    recurse(tree.child(n, 0), false)
  of mnkPathArray:
    let typ = env.types.canonical(tree[n, 0].typ)
    let desc = env.types.headerFor(typ, Canonical)
    case desc.kind
    of tkArray, tkUncheckedArray:
      wrapCopy At:
        recurse(tree.child(n, 0), false)
        recurse(tree.child(n, 1), true)
    of tkCstring:
      wrapCopy At:
        bu.subTree Deref:
          bu.add node(Type, c.genFlexArrayType(env.types, CharType))
          recurse(tree.child(n, 0), true)
        recurse(tree.child(n, 1), true)
    of tkSeq, tkString:
      wrapCopy At:
        bu.subTree Field:
          bu.subTree Deref:
            bu.add typeRef(c, env, payloadType(env.types, typ))
            bu.subTree Copy:
              bu.subTree Field:
                recurse(tree.child(n, 0), false)
                bu.add node(Immediate, 1)
          bu.add node(Immediate, 1)
        recurse(tree.child(n, 1), true)
    of tkOpenArray:
      wrapCopy At:
        bu.subTree Deref:
          bu.add node(Type, c.genFlexArrayType(env.types, elem(desc)))
          bu.subTree Copy:
            bu.subTree Field:
              recurse(tree.child(n, 0), false)
              bu.add node(Immediate, 0)
        recurse(tree.child(n, 1), true)
    else:
      unreachable()
  of mnkPathConv:
    const PointerLike = {tkVar, tkLent, tkRef, tkPtr}
    let a = env.types.canonical(tree[n].typ)
    let b = env.types.canonical(tree[n, 0].typ)
    if a == b:
      # same canonical type (happens for lvalue conversions involving
      # ``distinct`` types); a no-op
      recurse(tree.child(n, 0), wantValue)
    else:
      # either an object up- or down-conversion
      let diff = inheritanceDiff(env.types[a].skipTypes(skipPtrs),
                                 env.types[b].skipTypes(skipPtrs))
      if diff < 0:
        # it's an up conversion. The argument may be either a pointer-to-object
        # or object

        proc emit(c; env; tree; n; diff: int, src: TypeId, bu) {.nimcall.} =
          if diff == 0:
            let desc = env.types.headerFor(src, Lowered)
            if desc.kind in PointerLike:
              bu.subTree Deref:
                bu.add typeRef(c, env, desc.elem())
                recurse(n, true)
            else:
              recurse(n, false)
          else:
            bu.subTree Field:
              emit(c, env, tree, n, diff + 1, src, bu)
              bu.add node(Immediate, 0)

        if env.types.headerFor(b, Lowered).kind in PointerLike:
          bu.subTree Addr:
            emit(c, env, tree, tree.child(n, 0), diff, b, bu)
        else:
          wrapCopy:
            emit(c, env, tree, tree.child(n, 0), diff, b, bu)
      else:
        if env.types.headerFor(b, Lowered).kind in PointerLike:
          # there are no pointer types in the IL; nothing to do
          recurse(tree.child(n, 0), wantValue)
        else:
          assert not wantValue
          bu.subTree Deref:
            bu.add typeRef(c, env, a)
            bu.subTree Addr:
              recurse(tree.child(n, 0), false)

  of mnkStrLit, mnkAstLit:
    unreachable()
  of AllNodeKinds - LvalueExprKinds - LiteralDataNodes - {mnkProcVal}:
    unreachable($tree[n].kind)

proc gen(c; env: MirEnv, tree; n; wantsValue: bool): Expr =
  ## Translates the MIR value expression into IL code and returns it as an
  ## `Expr`.
  var bu = initBuilder[NodeKind]()
  c.translateValue(env, tree, n, wantsValue, bu)
  result = makeExpr(finish(bu), tree[n].typ)
  assert result.nodes.len > 0

proc getTypeInfoV2(c; env: var MirEnv, typ: TypeId): Expr =
  ## Returns a pointer expression referring to the RTTI global for `typ`.
  ## The RTTI data is created first if it wasn't already.
  let rttiType = env.types.add(c.graph.getCompilerProc("TNimTypeV2").typ)

  var global: uint32
  c.rttiCache.withValue typ, val:
    global = val[]
  do:
    let data = genTypeInfoV2(env, c.graph, typ)
    c.dataMap.withValue data, id:
      global = id[]
    do:
      global = c.newGlobal(env, rttiType)
      c.dataMap[data] = global

    c.rttiCache[typ] = global

  result = makeExpr PointerType:
    bu.subTree Copy:
      bu.add node(Global, global)

proc genDefault(c; env: var MirEnv; dest: Expr, typ: TypeId, bu) =
  let typ = env.types.canonical(typ)
  case env.types.headerFor(typ, Lowered).kind
  of tkBool, tkChar, tkInt, tkUInt, tkRef, tkPtr, tkVar, tkLent, tkPointer:
    genAsgn(dest, makeExpr(@[node(IntVal, c.lit.pack(0))], typ), bu)
  of tkFloat:
    genAsgn(dest, makeExpr(@[node(FloatVal, c.lit.pack(0.0))], typ), bu)
  else:
    let size = env.types.headerFor(typ, Lowered).size(env.types)
    bu.subTree Clear:
      takeAddr(dest, bu)
      bu.add node(IntVal, c.lit.pack(size))

    # TODO: the original type has to be passed to both hasRttiHeader and
    #       getTypeInfoV2, otherwise distinct types don't have the
    #       correct RTTI generated for them
    if hasRttiHeader(env.types, typ):
      bu.subTree Asgn:
        c.genField(env, dest, -1, bu)
        bu.use c.getTypeInfoV2(env, typ)

    # TODO: implement initialization for RTTI headers in embedded types

proc genField(c; env: MirEnv; tree; n; pos: int32, bu) =
  c.genField(env, c.gen(env, tree, n, false), pos, bu)

proc genOf(c; env: var MirEnv, tree; e: Expr, typ: TypeId; bu) =
  bu.subTree Call:
    bu.add compilerProc(c, env, "isObj")
    bu.subTree Copy:
      c.genField(env, e, -1, bu)

    # fetch the type name from the RTTI object
    # TODO: use the name cstring directly, without first requesting an RTTI
    #       object
    let rttiType = env.types.add(c.graph.getCompilerProc("TNimTypeV2").typ)
    bu.subTree Copy:
      bu.subTree Field:
        bu.subTree Deref:
          bu.add typeRef(c, env, rttiType)
          bu.use c.getTypeInfoV2(env, typ)
        bu.add node(Immediate, 3)

proc genLength(c; env: var MirEnv; tree; n; dest: Expr, stmts) =
  ## Emits an assignment between `dest` and a length query for `n`.
  let typ = env.types.canonical(tree[n].typ)
  case env.types.headerFor(typ, Canonical).kind
  of tkSeq, tkString:
    stmts.putInto dest, Copy:
      bu.subTree Field:
        c.translateValue(env, tree, n, false, bu)
        bu.add node(Immediate, 0)
  of tkArray:
    # XXX: we need to know about empty arrays here, but the MIR array type
    #      length is always clamped to 1 and thus we cannot rely on it.
    #      `mirgen` should special-case empty arrays in mSlice operations
    let L = c.graph.config.lengthOrd(env.types[typ]).toInt
    stmts.putInto dest, node(IntVal, c.lit.pack(L))
  of tkOpenArray:
    stmts.putInto dest, Copy:
      bu.subTree Field:
        c.translateValue(env, tree, n, false, bu)
        bu.add node(Immediate, 1)
  of tkCstring:
    # generate ``if x.isNil: 0 else: nimCStrLen(x)``
    let
      then = c.prc.newLabel()
      els  = c.prc.newLabel()
      exit = c.prc.newLabel()
    stmts.addStmt Branch:
      bu.subTree Eq:
        bu.add typeRef(c, env, CstringType)
        c.translateValue(env, tree, n, true, bu)
        bu.add node(IntVal, 0)
      bu.goto els
      bu.goto then
    stmts.join then
    stmts.putInto dest, node(IntVal, 0)
    stmts.goto exit
    stmts.join els
    stmts.putInto dest, Call:
      bu.add compilerProc(c, env, "nimCStrLen")
      c.translateValue(env, tree, n, true, bu)
    stmts.join exit
  else:
    unreachable()

proc genSetElem(c; env; tree; n; styp: TypeId, bu) =
  ## Emits the expression for loading a value for use in a set-related
  ## operation. This means turning the value into one relative to the start of
  ## the set's value range. The resulting value is always of uint16 type.
  proc aux(c; env; tree; n; styp: TypeId, bu) =
    assert env.types[styp].kind == tySet
    let first = c.graph.config.firstOrd(env.types[styp])
    if first != Zero:
      bu.subTree Sub:
        bu.add typeRef(c, env, tree[n].typ)
        c.translateValue(env, tree, n, true, bu)
        bu.add node(IntVal, c.lit.pack(first.toInt))
    else:
      c.translateValue(env, tree, n, true, bu)

  let typ = env.types.canonical(tree[n].typ)
  let desc = env.types.headerFor(typ, Lowered)
  if desc.kind != tkUInt or desc.size(env.types) != 2:
    # sets cannot have more than 2^16 elements, hence a uint16
    bu.subTree Conv:
      bu.add node(UInt, 2)
      bu.add typeRef(c, env, typ)
      aux(c, env, tree, n, styp, bu)
  else:
    aux(c, env, tree, n, styp, bu)

proc genSetOp(c; env: var MirEnv, tree; n; dest: Expr, stmts) =
  ## Generates and emits the IL code for a binary set operation.
  let
    a = NodePosition tree.argument(n, 0) # always a set
    b = NodePosition tree.argument(n, 1)
    # ^^ for some operations a set, for others not
    m = tree[n, 1].magic
    typ  = env.types.canonical(tree[a].typ)
    desc = env.types.headerFor(typ, Lowered)

  # sets with a number of elements <= 64 fit into unsigned integers. All
  # other sets are implemented as an array of small sets (i.e., sets with
  # 8 elements, fitting into a uint8)

  template value(n: NodePosition) =
    c.translateValue(env, tree, n, true, bu)

  template takeAddr(n: NodePosition) =
    takeAddr(c.gen(env, tree, n, false), bu)

  template elem(n: NodePosition) =
    # watch out! Don't use the canonical set type, because then the set
    # range's start value cannot be looked up anymore
    c.genSetElem(env, tree, n, tree[a].typ, bu)

  template lenValue() =
    let L = env.types.headerFor(typ, Lowered).arrayLen(env.types)
    bu.add node(IntVal, c.lit.pack(L))

  if desc.kind == tkArray:
    case m
    of mMulSet, mPlusSet, mMinusSet:
      const Ops = [mMulSet: "skullyMulSet",
                   mPlusSet: "skullyPlusSet",
                   mMinusSet: "skullMinusSet"]
      stmts.addStmt Call:
        bu.add compilerProc(c, env, Ops[m])
        takeAddr(dest, bu)
        takeAddr a
        takeAddr b
        lenValue()
    of mEqSet:
      stmts.putInto dest, Eq:
        bu.add typeRef(c, env, BoolType)
        bu.subTree Call:
          bu.add compilerProc(c, env, "nimCmpMem")
          takeAddr a
          takeAddr b
          lenValue()
        bu.add node(IntVal, c.lit.pack(0))
    of mLeSet, mLtSet:
      const Ops = [mLeSet: "skullyLeSet", mLtSet: "skullyLtSet"]
      stmts.putInto dest, Call:
        bu.add compilerProc(c, env, Ops[m])
        takeAddr a
        takeAddr b
        lenValue()
    of mIncl, mExcl:
      const Ops = [mIncl: "skullyIncl", mExcl: "skullyExcl"]
      stmts.putInto dest, Call:
        bu.add compilerProc(c, env, Ops[m])
        takeAddr a
        elem b
    of mInSet:
      stmts.putInto dest, Call:
        bu.add compilerProc(c, env, "skullyInSet")
        takeAddr a
        elem b
    else:
      unreachable()
  else:
    case m
    of mMulSet:
      stmts.putInto dest, BitAnd:
        bu.add typeRef(c, env, typ)
        value a
        value b
    of mPlusSet:
      stmts.putInto dest, BitOr:
        bu.add typeRef(c, env, typ)
        value a
        value b
    of mMinusSet:
      stmts.putInto dest, BitAnd:
        bu.add typeRef(c, env, typ)
        value a
        bu.subTree BitNot:
          bu.add typeRef(c, env, typ)
          value b
    of mEqSet:
      stmts.putInto dest, Eq:
        bu.add typeRef(c, env, typ)
        value a
        value b
    of mLtSet:
      # generate ``((a and not b) == 0) and (a != b)``
      let
        els  = c.prc.newLabel()
        then = c.prc.newLabel()
        next = c.prc.newLabel()
      stmts.addStmt Branch:
        bu.subTree Eq:
          bu.add typeRef(c, env, typ)
          bu.subTree BitAnd:
            bu.add typeRef(c, env, typ)
            value a
            bu.subTree BitNot:
              bu.add typeRef(c, env, typ)
              value b
          bu.add node(IntVal, c.lit.pack(0))
        bu.goto els
        bu.goto then
      stmts.join then
      stmts.putInto dest, Not:
        bu.subTree Eq:
          bu.add typeRef(c, env, typ)
          value a
          value b
      stmts.goto next
      stmts.join els
      stmts.putInto dest, node(IntVal, c.lit.pack(0))
      stmts.join next
    of mLeSet:
      # generate ``(a and not b) == 0``
      stmts.putInto dest, Eq:
        bu.add typeRef(c, env, typ)
        bu.subTree BitAnd:
          bu.add typeRef(c, env, typ)
          value a
          bu.subTree BitNot:
            bu.add typeRef(c, env, tree[b].typ)
            value b
        bu.add node(IntVal, c.lit.pack(0))
    of mIncl:
      # generate ``dest = dest or (1 shl elem)``
      let dest = c.gen(env, tree, a, false)
      stmts.putInto dest, BitOr:
        bu.add typeRef(c, env, typ)
        bu.use dest
        bu.subTree Shl:
          bu.add typeRef(c, env, typ)
          bu.add node(IntVal, c.lit.pack(1))
          elem b
    of mExcl:
      # generate ``dest = dest and not (1 shl elem)``
      let dest = c.gen(env, tree, a, false)
      stmts.putInto dest, BitAnd:
        bu.add typeRef(c, env, typ)
        bu.use dest
        bu.subTree BitNot:
          bu.add typeRef(c, env, typ)
          bu.subTree Shl:
            bu.add typeRef(c, env, typ)
            bu.add node(IntVal, c.lit.pack(1))
            elem b
    of mInSet:
      # generate ``(set bitand (1 shl elem)) != 0``
      stmts.putInto dest, Not:
        bu.subTree Eq:
          bu.add typeRef(c, env, typ)
          bu.subTree BitAnd:
            bu.add typeRef(c, env, typ)
            value a
            bu.subTree Shl:
              bu.add typeRef(c, env, typ)
              bu.add node(IntVal, c.lit.pack(1))
              elem b
          bu.add node(IntVal, c.lit.pack(0))
    else:
      unreachable()

proc genMagic(c; env: var MirEnv, tree; n; dest: Expr, stmts) =
  template value(n: NodePosition) =
    c.translateValue(env, tree, n, true, bu)

  template lvalue(n: OpValue) =
    c.translateValue(env, tree, NodePosition(n), false, bu)

  template value(n: OpValue) =
    value(NodePosition n)

  template takeAddr(n: NodePosition) =
    takeAddr(c.gen(env, tree, n, false), bu)

  template wrapAsgn(k: NodeKind, body: untyped) =
    stmts.putInto dest, k, body

  template wrapAsgn(body: untyped) =
    if true:
      var bu {.inject.} = initBuilder[NodeKind]()
      body
      genAsgn(dest, makeExpr(finish(bu), dest.typ), stmts)

  case tree[n, 1].magic
  of mNot:
    wrapAsgn Not:
      value(tree.argument(n, 0))
  of mLtI, mLtF64, mLtEnum, mLtU, mLtCh, mLtPtr:
    wrapAsgn Lt:
      bu.add typeRef(c, env, tree[tree.argument(n, 0)].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mLeI, mLeF64, mLeEnum, mLeU, mLeCh, mLePtr:
    wrapAsgn Le:
      bu.add typeRef(c, env, tree[tree.argument(n, 0)].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mEqI, mEqF64, mEqEnum, mEqRef, mEqCh, mEqB:
    wrapAsgn Eq:
      bu.add typeRef(c, env, tree[tree.argument(n, 0)].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mEqProc:
    let typ = env.types.canonical(tree[tree.argument(n, 0)].typ)
    if env.types.headerFor(typ, Lowered).kind == tkProc:
      # simple integer equality suffices
      wrapAsgn Eq:
        bu.add typeRef(c, env, typ)
        value(tree.argument(n, 0))
        value(tree.argument(n, 1))
    else:
      # both the procedure pointer and environment pointer need to be
      # compared (shallow equality)
      # TODO: use a proper short-circuiting ``and``, not a ``bitand``
      wrapAsgn BitAnd:
        bu.add typeRef(c, env, PointerType)
        wrapAsgn Eq:
          bu.add typeRef(c, env, PointerType)
          bu.subTree Copy:
            bu.subTree Field:
              lvalue tree.argument(n, 0)
              bu.add node(Immediate, 0)
          bu.subTree Copy:
            bu.subTree Field:
              lvalue tree.argument(n, 1)
              bu.add node(Immediate, 0)
        wrapAsgn Eq:
          bu.add typeRef(c, env, PointerType)
          bu.subTree Copy:
            bu.subTree Field:
              lvalue tree.argument(n, 0)
              bu.add node(Immediate, 1)
          bu.subTree Copy:
            bu.subTree Field:
              lvalue tree.argument(n, 1)
              bu.add node(Immediate, 1)
  of mIsNil:
    wrapAsgn Eq:
      let arg = tree.argument(n, 0)
      case env.types.headerFor(tree[arg].typ, Lowered).kind
      of tkClosure:
        bu.add typeRef(c, env, tree[arg].typ)
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(arg)
            bu.add node(Immediate, 0)
      else:
        # must be a pointer-like type
        bu.add typeRef(c, env, tree[arg].typ)
        value(arg)
      bu.add node(IntVal, 0)
  of mAddU, mSubU, mMulU, mDivU, mModU:
    const Map = [mAddU: Add, mSubU: Sub, mMulU: Mul, mDivU: Div, mModU: Mod]
    wrapAsgn Map[tree[n, 1].magic]:
      bu.add typeRef(c, env, tree[n].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mBitandI:
    wrapAsgn BitAnd:
      bu.add typeRef(c, env, tree[n].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mBitxorI:
    wrapAsgn BitXor:
      bu.add typeRef(c, env, tree[n].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mBitnotI:
    wrapAsgn BitNot:
      bu.add typeRef(c, env, tree[n].typ)
      value(tree.argument(n, 0))
  of mBitorI:
    wrapAsgn BitOr:
      bu.add typeRef(c, env, tree[n].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mShlI:
    wrapAsgn Shl:
      bu.add typeRef(c, env, tree[n].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mAshrI, mShrI:
    wrapAsgn Shr:
      bu.add typeRef(c, env, tree[n].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mOrd:
    wrapAsgn:
      value(tree.argument(n, 0))
  of mChr:
    wrapAsgn Conv:
      bu.add typeRef(c, env, tree[n].typ)
      bu.add typeRef(c, env, tree[tree.argument(n, 0)].typ)
      value(tree.argument(n, 0))
  of mIncl, mExcl, mLtSet, mLeSet, mEqSet, mMinusSet, mPlusSet, mMulSet,
     mInSet:
    c.genSetOp(env, tree, n, dest, stmts)
  of mCard:
    let a = tree.argument(n, 0)
    let desc = env.types.headerFor(env.types.canonical(tree[a].typ), Lowered)
    if desc.kind == tkArray:
      wrapAsgn Call:
        bu.add compilerProc(c, env, "skullyCard")
        takeAddr NodePosition(a)
        bu.add node(IntVal, c.lit.pack(desc.size(env.types)))
    elif desc.size(env.types) == 8:
      wrapAsgn Call:
        bu.add compilerProc(c, env, "countBits64")
        value a
    elif desc.size(env.types) == 4:
      wrapAsgn Call:
        bu.add compilerProc(c, env, "countBits32")
        value a
    else:
      # also use countBits32, but widen the operand first
      wrapAsgn Call:
        bu.add compilerProc(c, env, "countBits32")
        bu.subTree Conv:
          bu.add node(UInt, 4)
          bu.add typeRef(c, env, tree[a].typ)
          value a
  of mDefault:
    c.genDefault(env, dest, tree[n].typ, stmts)
  of mMaxI, mMinI:
    let a = c.prc.newLabel()
    let b = c.prc.newLabel()
    let after = c.prc.newLabel()
    stmts.addStmt Branch:
      var (arg1, arg2) =
        if tree[n, 1].magic == mMaxI:
          (0, 1)
        else:
          (1, 0)

      bu.subTree Lt:
        bu.add typeRef(c, env, tree[n].typ)
        value(tree.argument(n, arg1))
        value(tree.argument(n, arg2))
      bu.goto(b)
      bu.goto(a)
    stmts.join(a) # then branch
    wrapAsgn:
      value(tree.argument(n, 1))
    stmts.goto(after)
    stmts.join(b) # else branch
    wrapAsgn:
      value(tree.argument(n, 0))
    stmts.join(after)
  of mSizeof:
    let typ = env.types.canonical(tree[tree.argument(n, 0)].typ)
    let desc = env.types.headerFor(typ, Canonical)
    if desc.size(env.types) >= 0:
      wrapAsgn:
        bu.add node(IntVal, c.lit.pack(desc.size(env.types)))
    else:
      unreachable()
  of mAlignof:
    let typ = env.types.canonical(tree[tree.argument(n, 0)].typ)
    let desc = env.types.headerFor(typ, Canonical)
    if desc.size(env.types) >= 0:
      wrapAsgn:
        bu.add node(IntVal, c.lit.pack(desc.align))
    else:
      unreachable()
  of mEqStr:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "eqStrings")
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mLeStr:
    wrapAsgn Le:
      bu.add typeRef(c, env, env.types.sizeType)
      bu.subTree Call:
        bu.add compilerProc(c, env, "cmpStrings")
        value(tree.argument(n, 0))
        bu.add node(IntVal, 0)
  of mLtStr:
    wrapAsgn Lt:
      bu.add typeRef(c, env, env.types.sizeType)
      bu.subTree Call:
        bu.add compilerProc(c, env, "cmpStrings")
        value(tree.argument(n, 0))
        bu.add node(IntVal, 0)
  of mFinished:
    # the status field is stored at the start of the env object, load it and
    # test whether the value is < 0
    wrapAsgn Lt:
      bu.add typeRef(c, env, env.types.sizeType)
      bu.subTree Load:
        bu.add typeRef(c, env, env.types.sizeType)
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(tree.argument(n, 0))
            bu.add node(Immediate, 1)

      bu.add node(IntVal, 0)
  of mCopyInternal:
    # the internal part of an object is the RTTI pointer stored in the hidden
    # field
    stmts.addStmt Asgn:
      c.genField(env, tree, NodePosition tree.argument(n, 0), -1, bu)
      bu.subTree Copy:
        c.genField(env, tree, NodePosition tree.argument(n, 1), -1, bu)
  of mArrToSeq:
    let
      seqType  = env.types.canonical(tree[n].typ)
      arg      = env.types.canonical(tree[tree.argument(n, 0)].typ)
      elem     = env.types.canonical(env.types.headerFor(arg, Canonical).elem)
      elemDesc = env.types.headerFor(elem, Canonical)
      len      = c.graph.config.lengthOrd(env.types[arg]).toInt
    # emit the length initialization:
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 0)
      bu.add node(IntVal, c.lit.pack(len))
    # emit the seq allocation:
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 1)
      bu.subTree Call:
        bu.add compilerProc(c, env, "newSeqPayload")
        bu.add node(IntVal, c.lit.pack len)
        bu.add node(IntVal, c.lit.pack elemDesc.size(env.types))
        bu.add node(IntVal, c.lit.pack elemDesc.align)

    if len < 10:
      for i in 0..<len:
        stmts.addStmt Asgn:
          bu.subTree At:
            bu.subTree Field:
              bu.subTree Deref:
                bu.add typeRef(c, env, payloadType(env.types, seqType))
                bu.use dest
              bu.add node(Immediate, 1)
            bu.add node(IntVal, c.lit.pack(i))
          bu.subTree Copy:
            bu.subTree At:
              lvalue tree.argument(n, 0)
              bu.add node(IntVal, c.lit.pack(i))
    else:
      # too many elements. Use a blit copy in order to not explode code size
      stmts.addStmt Blit:
        bu.subTree Addr:
          bu.subTree Field:
            bu.subTree Deref:
              bu.add typeRef(c, env, payloadType(env.types, seqType))
              bu.subTree Copy:
                bu.subTree Field:
                  bu.useLvalue dest
                  bu.add node(Immediate, 1)
            bu.add node(Immediate, 1)
        takeAddr NodePosition(tree.argument(n, 0))
        bu.add node(IntVal, c.lit.pack(len * elemDesc.size(env.types)))
  of mSamePayload:
    wrapAsgn Eq:
      bu.add typeRef(c, env, PointerType)
      bu.subTree Copy:
        bu.subTree Field:
          lvalue(tree.argument(n, 0))
          bu.add node(Immediate, 1)
      bu.subTree Copy:
        bu.subTree Field:
          lvalue(tree.argument(n, 1))
          bu.add node(Immediate, 1)
  of mLengthSeq, mLengthOpenArray, mLengthStr:
    c.genLength(env, tree, NodePosition tree.argument(n, 0), dest, stmts)
  of mHigh:
    let tmp = c.newTemp(env.types.sizeType)
    c.genLength(env, tree, NodePosition tree.argument(n, 0), tmp, stmts)
    wrapAsgn Sub:
      bu.add typeRef(c, env, env.types.sizeType)
      bu.use tmp
      bu.add node(IntVal, 1)
  of mSetLengthStr:
    stmts.addStmt Call:
      bu.add compilerProc(c, env, "setLengthStrV2")
      takeAddr NodePosition(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mNewString:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "mnewString")
      value(tree.argument(n, 0))
  of mNewStringOfCap:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "rawNewString")
      value(tree.argument(n, 0))
  of mBoolToStr:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "nimBoolToStr")
      value(tree.argument(n, 0))
  of mCharToStr:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "nimCharToStr")
      value(tree.argument(n, 0))
  of mCStrToStr:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "cstrToNimstr")
      value(tree.argument(n, 0))
  of mStrToCStr:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "nimToCStringConv")
      value(tree.argument(n, 0))
  of mAppendStrStr:
    # in theory, the appendStrStr magic supports being merged, but this never
    # happens in practice, meaning that the call expression only ever has
    # two parameters here
    stmts.addStmt Call:
      bu.add compilerProc(c, env, "prepareAdd")
      takeAddr NodePosition(tree.argument(n, 0))
      bu.subTree Add:
        bu.add typeRef(c, env, env.types.sizeType)
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(tree.argument(n, 0))
            bu.add node(Immediate, 0)
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(tree.argument(n, 1))
            bu.add node(Immediate, 0)

    stmts.addStmt Call:
      bu.add compilerProc(c, env, "appendString")
      takeAddr NodePosition(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mConStrStr:
    var
      temp  = c.newTemp(StringType)
      nodes = newSeq[Node]()
    # manually construct the node sequence; it's simpler

    # compute the length expression:
    var i = 0
    for (_, _, it) in tree.arguments(n):
      if i < tree.numArgs(n) - 1:
        nodes.add node(Add, 3)
        nodes.add typeRef(c, env, env.types.sizeType)

      if tree[it].typ == CharType:
        nodes.add node(IntVal, 1)
      else:
        nodes.add node(Copy, 1)
        nodes.add node(Field, 2)
        nodes.add c.gen(env, tree, NodePosition(it), false).nodes
        nodes.add node(Immediate, 0)

      inc i

    stmts.addStmt Asgn:
      bu.useLvalue(temp)
      bu.subTree Call:
        bu.add compilerProc(c, env, "rawNewString")
        bu.add nodes # the length expression

    # emit the append calls:
    for (_, _, it) in tree.arguments(n):
      if tree[it].typ == CharType:
        stmts.addStmt Call:
          bu.add compilerProc(c, env, "appendChar")
          bu.subTree Addr:
            bu.useLvalue(temp)
          value(it)
      else:
        stmts.addStmt Call:
          bu.add compilerProc(c, env, "appendString")
          bu.subTree Addr:
            bu.useLvalue(temp)
          value(it)

    genAsgn(dest, temp, stmts)
  of mParseBiggestFloat:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "nimParseBiggestFloat")
      value(tree.argument(n, 0))
      takeAddr NodePosition(tree.argument(n, 1))
      value(tree.argument(n, 2))
  of mAppendStrCh:
    stmts.addStmt Call:
      bu.add compilerProc(c, env, "nimAddCharV1")
      takeAddr NodePosition(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mDestroy:
    let
      typ    = env.types.canonical(tree[tree.argument(n, 0)].typ)
      ptrTyp = env.types[env.types.lookupField(typ, 1)].typ
      els    = c.prc.newLabel()

    var then = c.prc.newLabel()

    # emit the following:
    #   if x.p != nil and (x.p.cap and NIM_STRLIT_FLAG) == 0:
    #     dealloc(x.p)
    stmts.addStmt Branch:
      bu.subTree Eq:
        bu.add typeRef(c, env, ptrTyp)
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(tree.argument(n, 0))
            bu.add node(Immediate, 0)
        bu.add node(IntVal, 0)
      bu.goto then
      bu.goto els
    stmts.join then
    then = c.prc.newLabel()
    stmts.addStmt Branch:
      bu.subTree Eq:
        bu.add typeRef(c, env, env.types.sizeType)
        bu.subTree BitAnd:
          bu.add typeRef(c, env, env.types.sizeType)
          bu.subTree Copy:
            bu.subTree Field:
              bu.subTree Deref:
                bu.add typeRef(c, env, elem env.types.headerFor(ptrTyp, Lowered))
                bu.subTree Copy:
                  bu.subTree Field:
                    lvalue(tree.argument(n, 0))
                    bu.add node(Immediate, 1)
              bu.add node(Immediate, 0)
          bu.add node(IntVal, c.lit.pack(StrLitFlag))
        bu.add node(IntVal, 0)
      bu.goto els
      bu.goto then

    stmts.join then
    case env.types.headerFor(typ, Canonical).kind
    of tkString:
      stmts.addStmt Call:
        bu.add compilerProc(c, env, "dealloc")
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(tree.argument(n, 0))
            bu.add node(Immediate, 1)
    of tkSeq:
      stmts.addStmt Call:
        bu.add compilerProc(c, env, "alignedDealloc")
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(tree.argument(n, 0))
            bu.add node(Immediate, 1)
        bu.add node(IntVal, c.lit.pack(env.types.headerFor(typ, Canonical).align))
    else:
      unreachable("destroy was not lowered?")

    stmts.join els
  of mExit:
    # TODO: implement properly
    discard
  of mEcho:
    # emit the array construction:
    let tmp = c.newTemp(tree[tree.argument(n, 0)].typ)
    for i in 1..<tree.numArgs(n):
      stmts.addStmt Asgn:
        bu.subTree At:
          bu.useLvalue(tmp)
          bu.add node(IntVal, c.lit.pack(i - 1))
        value(tree.argument(n, i))

    # emit the openArray construction:
    let
      prc = c.graph.getCompilerProc("echoBinSafe")
      oa  = c.newTemp(env.types.add(prc.typ[1]))

    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue oa
        bu.add node(Immediate, 0)
      bu.subTree Addr:
        bu.useLvalue tmp
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue oa
        bu.add node(Immediate, 1)
      bu.add node(IntVal, c.lit.pack(tree.numArgs(n) - 1))

    stmts.addStmt Call:
      bu.add compilerProc(c, env, "echoBinSafe")
      bu.use oa
  of mOf:
    var typ = tree[tree.argument(n, 1)].typ
    # the typ is a typedesc, and the only way to retrieve the inner type is
    # by going through the PType
    typ = env.types.add(env.types[typ].skipTypes(abstractPtrs))

    let e = c.gen(env, tree, NodePosition tree.argument(n, 0), false)
    case env.types.headerFor(env.types.canonical(e.typ), Canonical).kind
    of tkRecord:
      wrapAsgn:
        c.genOf(env, tree, e, typ, bu)
    of tkRef, tkPtr:
      # emit ``if p == nil: false else: p[] of typ``
      let
        then = c.prc.newLabel()
        els  = c.prc.newLabel()
        next = c.prc.newLabel()
      stmts.addStmt Branch:
        bu.subTree Eq:
          bu.add typeRef(c, env, e.typ)
          bu.use e
          bu.add node(IntVal, c.lit.pack(0))
        bu.goto els
        bu.goto then
      stmts.join then
      stmts.putInto dest, node(IntVal, c.lit.pack(0))
      stmts.goto next
      stmts.join els
      let
        elem = env.types.headerFor(env.types.canonical(e.typ), Canonical).elem
        objExpr = buildExpr elem:
          bu.subTree Deref:
            bu.add typeRef(c, env, elem)
            bu.use e
      wrapAsgn:
        c.genOf(env, tree, objExpr, typ, bu)
      stmts.join next
    else:
      unreachable()
  of mChckBounds:
    # XXX: bound checks on to-openArray conversion are currently omitted, as
    #      the implementation would simply be too error-prone at the moment
    #      (bound checks are fairly involved, see ``cgen`` in the NimSkull
    #      compiler)
    discard
  of mGetTypeInfoV2:
    let t = tree[tree.argument(n, 0)].typ
    if isFinal(env.types[t]):
      # static type information
      genAsgn(dest, c.getTypeInfoV2(env, t), stmts)
    else:
      # dynamic type information; query the object's type header
      wrapAsgn:
        c.genField(env, tree, NodePosition tree.argument(n, 0), -1, bu)
  else:
    # TODO: implement the remaining magics
    warn(c, tree[n].info, "magic not implemented: " & $tree[n, 1].magic)

proc genCall(c; env: var MirEnv; tree; n; dest: Expr, stmts; withEnv = false) =
  ## Translates a MIR call to its IL equivalent. When `withEnv` is true, the
  ## environment stored in the invoked closure is passed to the procedure.
  let kind =
    if tree[n].kind == mnkCall:
      Call
    elif tree[n].typ == VoidType:
      CheckedCall
    else:
      CheckedCallAsgn

  proc genOperands(c; env: var MirEnv; tree; n; bu; stmts;
                   withEnv: bool) {.nimcall.} =
    var typ: TypeId ## type of the callee

    if tree[n, 1].kind == mnkProc:
      # a static call
      typ = env.types.add(env[tree[n, 1].prc].typ)
      bu.add node(Proc, c.registerProc(tree[n, 1].prc))
    else:
      # a dynamic call
      typ = env.types.canonical(tree[n, 1].typ)
      let isClosure = env.types.headerFor(typ, Canonical).kind == tkClosure

      # for closure invocations where passing the env is omitted, the
      # signature type needs to have no env parameter too
      bu.add c.genProcType(env, typ, isClosure and not withEnv)
      if isClosure:
        bu.subTree Copy:
          bu.subTree Field:
            c.translateValue(env, tree, tree.child(n, 1), false, bu)
            bu.add node(Immediate, 0)
      else:
        c.translateValue(env, tree, tree.child(n, 1), true, bu)

    var i = 0
    for kind, _, it in tree.arguments(n):
      # ignore compile-time-only arguments
      if tree[it].kind != mnkNone:
        # note: not all pass-by-reference arguments use the ``mnkName`` mode
        if kind == mnkName or isPassByRef(env.types, typ, i):
          if tree[it].kind in LiteralDataNodes:
            # the expression doesn't have an address; introduce a temporary
            let tmp = c.newTemp(tree[it].typ)
            stmts.addStmt Asgn:
              bu.useLvalue tmp
              c.translateValue(env, tree, NodePosition it, true, bu)
            bu.subTree Addr:
              bu.useLvalue tmp
          else:
            takeAddr(c.gen(env, tree, NodePosition it, false), bu)
        else:
          c.translateValue(env, tree, NodePosition it, true, bu)

      inc i

    if withEnv:
      # pass the environment to the procedure
      bu.subTree Copy:
        bu.subTree Field:
          c.translateValue(env, tree, tree.child(n, 1), false, bu)
          bu.add node(Immediate, 1)

    if tree[n].kind == mnkCheckedCall:
      c.genExit(tree, tree.last(n), bu)

  if kind == CheckedCallAsgn:
    # go through a temporary
    let tmp = c.newTemp(tree[n].typ)
    stmts.addStmt CheckedCallAsgn:
      bu.useLvalue tmp
      c.genOperands(env, tree, n, bu, stmts, withEnv)

    genAsgn(dest, tmp, stmts)
  elif tree[n].typ == VoidType:
    stmts.addStmt kind:
      c.genOperands(env, tree, n, bu, stmts, withEnv)
  else:
    stmts.putInto dest, kind:
      c.genOperands(env, tree, n, bu, stmts, withEnv)

proc translateExpr(c; env: var MirEnv, tree; n; dest: Expr, stmts) =
  template value(n: NodePosition) =
    c.translateValue(env, tree, n, true, bu)

  template lvalue(n: NodePosition) =
    mixin bu
    c.translateValue(env, tree, n, false, bu)

  template takeAddr(n: NodePosition) =
    mixin bu
    takeAddr(c.gen(env, tree, n, false), bu)

  template wrapAsgn(k: NodeKind, body: untyped) =
    stmts.putInto dest, k, body

  template wrapAsgn(body: untyped) =
    if true:
      var bu {.inject.} = initBuilder[NodeKind]()
      body
      genAsgn(dest, makeExpr(finish(bu), dest.typ), stmts)

  case tree[n].kind
  of LvalueExprKinds, LiteralDataNodes, mnkProcVal:
    wrapAsgn:
      value(n)
  of mnkConv, mnkStdConv:
    wrapAsgn Conv:
      bu.add typeRef(c, env, tree[n].typ)
      bu.add typeRef(c, env, tree[n, 0].typ)
      value(tree.child(n, 0))
  of mnkCopy, mnkMove, mnkSink:
    wrapAsgn:
      value(tree.child(n, 0))
  of mnkCall, mnkCheckedCall:
    let callee = tree.callee(n)
    if tree[callee].kind == mnkMagic:
      c.genMagic(env, tree, n, dest, stmts)
    else:
      if tree[callee].kind == mnkProc:
        c.genCall(env, tree, n, dest, stmts)
      else:
        # a dynamic call. Closures require special handling, as the dynamic
        # callee might not have an env parameter. If the closure's env value
        # is non-nil, the dynamic callee must have one, otherwise it must not
        if env.types.headerFor(tree[callee].typ, Canonical).kind == tkClosure:
          let els  = c.prc.newLabel()
          let then = c.prc.newLabel()
          let exit = c.prc.newLabel()
          stmts.addStmt Branch:
            bu.subTree Eq:
              bu.add typeRef(c, env, PointerType)
              bu.subTree Copy:
                bu.subTree Field:
                  lvalue callee
                  bu.add node(Immediate, 1)
              bu.add node(IntVal, c.lit.pack(0))
            bu.goto els
            bu.goto then
          stmts.join then
          c.genCall(env, tree, n, dest, stmts, withEnv = false)
          stmts.goto exit
          stmts.join els
          c.genCall(env, tree, n, dest, stmts, withEnv = true)
          stmts.join exit
        else:
          c.genCall(env, tree, n, dest, stmts)
  of mnkAddr, mnkView, mnkMutView:
    wrapAsgn:
      takeAddr tree.child(n, 0)
  of mnkAdd, mnkSub, mnkMul, mnkDiv, mnkModI:
    const Map = [mnkAdd: Add, mnkSub: Sub, mnkMul: Mul, mnkDiv: Div, mnkModI: Mod]
    wrapAsgn Map[tree[n].kind]:
      bu.add typeRef(c, env, tree[n, 0].typ)
      value(tree.child(n, 0))
      value(tree.child(n, 1))
  of mnkNeg:
    wrapAsgn Neg:
      bu.add typeRef(c, env, tree[n, 0].typ)
      value(tree.child(n, 0))
  of mnkObjConstr:
    c.genDefault(env, dest, tree[n].typ, stmts)

    for it in tree.items(n, 0, ^1):
      stmts.addStmt Asgn:
        c.genField(env, dest, tree[it, 0].field, bu)
        value(tree.last(tree.child(it, 1)))
  of mnkTupleConstr, mnkClosureConstr:
    c.genDefault(env, dest, tree[n].typ, stmts)

    var i = 0
    for it in tree.items(n, 0, ^1):
      stmts.addStmt Asgn:
        bu.subTree Field:
          bu.useLvalue dest
          bu.add node(Immediate, i.uint32)
        value(tree.last(it))
      inc i
  of mnkArrayConstr:
    c.genDefault(env, dest, tree[n].typ, stmts)

    var i = 0
    for it in tree.items(n, 0, ^1):
      stmts.addStmt Asgn:
        bu.subTree At:
          bu.useLvalue dest
          bu.add node(IntVal, c.lit.pack(i))
        value(tree.last(it))
      inc i
  of mnkSeqConstr:
    let
      typ  = env.types.canonical(tree[n].typ)
      elem = env.types.headerFor(env.types.headerFor(typ, Canonical).elem(),
                                 Canonical)

    # emit the length initialization
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 0)
      bu.add node(IntVal, c.lit.pack(tree.len(n)))

    # emit the payload initialization:
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 1)
      bu.subTree Call:
        bu.add c.compilerProc(env, "newSeqPayload")
        bu.add node(IntVal, c.lit.pack(tree.len(n)))
        bu.add node(IntVal, c.lit.pack(size(elem, env.types)))
        bu.add node(IntVal, c.lit.pack(elem.align))

    var i = 0
    for it in tree.items(n, 0, ^1):
      stmts.addStmt Asgn:
        bu.subTree At:
          bu.subTree Field:
            bu.subTree Deref:
              bu.add typeRef(c, env, payloadType(env.types, typ))
              bu.subTree Copy:
                bu.subTree Field:
                  bu.useLvalue dest
                  bu.add node(Immediate, 1)
            bu.add node(Immediate, 1)
          bu.add node(IntVal, c.lit.pack(i))
        value(tree.child(it, 0))
      inc i

  of mnkToMutSlice, mnkToSlice:
    let
      typ  = env.types.canonical(tree[n, 0].typ)
      els  = c.prc.newLabel()
      then = c.prc.newLabel()
      exit = c.prc.newLabel()

    # emit the data pointer initialization:
    let dataExpr = makeExpr PointerType:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 0)

    let startExpr = makeExpr env.types.sizeType:
      if tree[n].len == 1:
        bu.add node(IntVal, c.lit.pack(0))
      else:
        value tree.child(n, 1)

    stmts.addStmt Branch:
      bu.subTree Le:
        bu.add typeRef(c, env, env.types.sizeType)
        if tree[n].len == 1:
          let tmp = c.newTemp(env.types.sizeType)
          c.genLength(env, tree, tree.child(n, 0), tmp, stmts)

          bu.add node(IntVal, c.lit.pack(0))
          bu.use tmp
        else:
          value tree.child(n, 1)
          value tree.child(n, 2)
      bu.goto(els)
      bu.goto(then)

    stmts.join(then)

    # emit the data pointer initialization:
    case env.types.headerFor(typ, Canonical).kind
    of tkCstring:
      stmts.putInto dataExpr, Addr:
        bu.subTree At:
          bu.subTree Deref:
            bu.add node(Type, c.genFlexArrayType(env.types, CharType))
            value tree.child(n, 0)
        bu.use startExpr
    of tkPtr:
      # can only be a pointer to an unchecked array
      let arr  = env.types.headerFor(typ, Canonical).elem
      stmts.putInto dataExpr, Addr:
        bu.subTree At:
          bu.subTree Deref:
            bu.add c.typeRef(env, arr)
            value tree.child(n, 0)
        bu.use startExpr
    of tkArray:
      stmts.putInto dataExpr, Addr:
        bu.subTree At:
          lvalue tree.child(n, 0)
          bu.use startExpr
    of tkSeq, tkString:
      stmts.putInto dataExpr, Addr:
        bu.subTree At:
          bu.subTree Field:
            bu.subTree Deref:
              bu.add typeRef(c, env, payloadType(env.types, typ))
              bu.subTree Copy:
                bu.subTree Field:
                  lvalue tree.child(n, 0)
                  bu.add node(Immediate, 1)
            bu.add node(Immediate, 1)
          bu.use startExpr
    of tkOpenArray:
      stmts.putInto dataExpr, Addr:
        bu.subTree At:
          bu.subTree Field:
            lvalue tree.child(n, 0)
            bu.add node(Immediate, 0)
          bu.use startExpr
    else:
      unreachable()

    # emit the length field initialization:
    if tree[n].len == 1:
      # the length is provided by the operand
      let nDest = makeExpr env.types.sizeType:
        bu.subTree Field:
          bu.useLvalue dest
          bu.add node(Immediate, 1)
      let tmp = c.newTemp(env.types.sizeType)
      c.genLength(env, tree, tree.child(n, 0), tmp, stmts)
      genAsgn(nDest, tmp, stmts)
    else:
      stmts.addStmt Asgn:
        bu.subTree Field:
          bu.useLvalue dest
          bu.add node(Immediate, 1)
        bu.subTree Add:
          bu.add typeRef(c, env, env.types.sizeType)
          bu.subTree Sub:
            bu.add typeRef(c, env, env.types.sizeType)
            value tree.child(n, 2)
            value tree.child(n, 1)
          bu.add node(IntVal, c.lit.pack(1))

    stmts.goto(exit)

    stmts.join(els)
    # if the requested length is zero, both the length and pointer are
    # initialized to zero
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 0)
      bu.add node(IntVal, c.lit.pack(0))
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.useLvalue dest
        bu.add node(Immediate, 1)
      bu.add node(IntVal, c.lit.pack(0))
    stmts.join(exit)
  of mnkSetConstr:
    c.genDefault(env, dest, tree[n].typ, stmts)

    proc genIncl(c; env: var MirEnv; dest, elem: Expr, stmts) =
      let desc = env.types.headerFor(dest.typ, Lowered)
      if desc.kind == tkArray:
        stmts.addStmt Call:
          bu.add compilerProc(c, env, "skullyIncl")
          takeAddr(dest, bu)
          bu.use elem
      else:
        stmts.putInto dest, BitOr:
          bu.add typeRef(c, env, dest.typ)
          bu.use dest
          bu.subTree Shl:
            bu.add typeRef(c, env, dest.typ)
            bu.add node(IntVal, c.lit.pack(1))
            bu.use elem

    for it in tree.items(n, 0, ^1):
      if tree[it].kind == mnkRange:
        # a range constructor. Include all elements part of the range in the
        # set
        let
          startLab = c.prc.newLabel()
          exitLab = c.prc.newLabel()
          bodyLab = c.prc.newLabel()
          idx = c.newTemp(UInt16Type)

        stmts.addStmt Asgn:
          bu.useLvalue idx
          c.genSetElem(env, tree, tree.child(it, 0), tree[n].typ, bu)

        stmts.join(startLab)
        stmts.addStmt Branch:
          bu.subTree Le:
            bu.add node(UInt, 2)
            bu.use idx
            c.genSetElem(env, tree, tree.child(it, 1), tree[n].typ, bu)
          bu.goto(exitLab)
          bu.goto(bodyLab)

        stmts.join(bodyLab)
        c.genIncl(env, dest, idx, stmts)

        # increment the index:
        stmts.addStmt Asgn:
          bu.useLvalue(idx)
          bu.subTree Add:
            bu.add node(UInt, 8)
            bu.use(idx)
            bu.add node(IntVal, 1)

        stmts.addStmt Loop:
          bu.add node(Immediate, startLab)
        stmts.join(exitLab)
      else:
        let e = makeExpr tree[it].typ:
          c.genSetElem(env, tree, it, tree[n].typ, bu)
        c.genIncl(env, dest, e, stmts)
  of mnkCast:
    let dst = env.types.canonical(tree[n].typ)
    let src = env.types.canonical(tree[n, 0].typ)
    let tdst = c.genType(env.types, dst)
    let tsrc = c.genType(env.types, src)
    if tdst == tsrc:
      # a no-op; assign the source expression unchanged
      genAsgn(dest, c.gen(env, tree, tree.child(n, 0), true), stmts)
    elif env.types.headerFor(dst, Lowered).kind in {tkRecord, tkArray, tkUnion} or
         env.types.headerFor(src, Lowered).kind in {tkRecord, tkArray, tkUnion}:
      # either the target or source type is an aggregate type -> use a blit copy
      let size = min(env.types.headerFor(dst, Lowered).size(env.types),
                     env.types.headerFor(src, Lowered).size(env.types))
      stmts.addStmt Blit:
        takeAddr(dest, bu)
        takeAddr tree.child(n, 0)
        bu.add node(IntVal, c.lit.pack(size))
    else:
      template isUnsigned(id: TypeId): bool =
        env.types.headerFor(id, Lowered).kind in
          {tkPtr, tkPointer, tkRef, tkUInt, tkChar, tkBool}

      let a = env.types.headerFor(dst, Lowered).size(env.types)
      let b = env.types.headerFor(src, Lowered).size(env.types)
      # for the implementation, keep in mind that Reinterp only supports
      # operands of the same size. "Cutting off" bits only works with uint
      # values, requiring the operand to first be bitcast into a uint value of
      # the same size
      # XXX: translation for casts will become easier once the IL has more fine
      #      grained conversion operators
      if a == b: # same size, only reinterpret
        wrapAsgn Reinterp:
          bu.add typeRef(c, env, dst)
          bu.add typeRef(c, env, src)
          value tree.child(n, 0)
      elif isUnsigned(dst):
        if isUnsigned(src):
          # a simple conversion (i.e., a zero extension) is enough
          wrapAsgn Conv:
            bu.add typeRef(c, env, dst)
            bu.add typeRef(c, env, src)
            value tree.child(n, 0)
        else:
          wrapAsgn Conv:
            bu.add typeRef(c, env, dst)
            bu.add node(UInt, b.uint32)
            bu.subTree Reinterp:
              bu.add node(UInt, b.uint32)
              bu.add typeRef(c, env, src)
              value tree.child(n, 0)
      elif isUnsigned(src):
        wrapAsgn Reinterp:
          bu.add typeRef(c, env, dst)
          bu.add node(UInt, a.uint32)
          bu.subTree Conv:
            bu.add node(UInt, a.uint32)
            bu.add typeRef(c, env, src)
            value tree.child(n, 0)
      else:
        wrapAsgn Reinterp:
          bu.add typeRef(c, env, dst)
          bu.add node(UInt, a.uint32)
          bu.subTree Conv:
            bu.add node(UInt, a.uint32)
            bu.add node(UInt, b.uint32)
            bu.subTree Reinterp:
              bu.add node(UInt, b.uint32)
              bu.add typeRef(c, env, src)
              value tree.child(n, 0)
  else:
    unreachable()

proc translateStmt(env: var MirEnv, tree; n; stmts; c) =
  template guardActive() =
    if not c.prc.active:
      return

  # XXX: the "is active" tracking is currently necessary because ``mirgen``
  #      doesn't perform local dead-code elimination correctly for closure
  #      iterators doesn't work

  case tree[n].kind
  of mnkAsgn, mnkSwitch, mnkDef, mnkDefCursor, mnkInit:
    guardActive()
    var dest = c.gen(env, tree, tree.child(n, 0), false)
    if tree[n, 0].kind == mnkPathVariant:
      # ``mnkPathVariant`` refers to the tag field here, *not* to the union
      let
        root = tree.child(n, 0)
        field = tree[root, 1].field
      # note: `tree[root].typ` yields the object type, even though it may
      # not look like it does
      let typ = env.types[env.types.lookupField(tree[root].typ, field)].typ
      dest = makeExpr typ:
        c.genField(env, dest, field, bu)

    if tree[n, 1].kind != mnkNone:
      c.translateExpr(env, tree, tree.child(n, 1), dest, stmts)
    elif tree[n, 0].kind != mnkParam:
      # ignore param defs; they only mark ``sink`` parameters as going live
      c.genDefault(env, dest, tree[n, 0].typ, stmts)
  of mnkBind, mnkBindMut:
    guardActive()
    c.prc.indirectLocals.incl tree[n, 0].local
    stmts.addStmt Asgn:
      bu.add node(Local, c.prc.localMap[tree[n, 0].local])
      takeAddr(c.gen(env, tree, tree.child(n, 1), false), bu)
  of mnkVoid:
    guardActive()
    c.translateExpr(env, tree, tree.child(n, 0), Expr(typ: VoidType), stmts)
    if tree[n, 0].kind in {mnkCall, mnkCheckedCall}:
      # handle noreturn calls; they need to be followed by an Unreachable
      let callee = tree.callee(tree.child(n, 0))
      if (tree[callee].kind == mnkMagic and tree[callee].magic == mExit) or
         (tree[callee].kind == mnkProc and
          sfNoReturn in env[tree[callee].prc].flags):
        stmts.addStmt Unreachable:
          discard
        c.prc.active = false
  of mnkScope, mnkEndScope:
    discard "nothing to do"
  of mnkLoop:
    guardActive()
    stmts.addStmt Loop:
      bu.add node(Immediate, c.prc.labelMap[tree[n, 0].label])
    c.prc.active = false
  of mnkIf:
    guardActive()
    let label = c.prc.newLabel()
    stmts.addStmt Branch:
      c.translateValue(env, tree, tree.child(n, 0), true, bu)
      c.genExit(tree, tree.child(n, 1), bu)
      bu.goto label
    stmts.join label
  of mnkEndStruct:
    var label: uint32
    # ``EndStruct`` can mark the end of both an ``If`` or ``Except``. Only
    # the ones marking the end of an ``If`` need to be turned into a join here
    if c.prc.labelMap.pop(tree[n, 0].label, label):
      stmts.join(label)
      c.prc.active = true
  of mnkGoto:
    guardActive()
    stmts.goto(c.prc.request(tree[n, 0].label))
    c.prc.active = false
  of mnkJoin:
    var label: uint32
    if c.prc.labelMap.pop(tree[n, 0].label, label):
      stmts.join(label)
      c.prc.active = true
  of mnkLoopJoin:
    guardActive()
    let label = c.prc.newLabel()
    c.prc.labelMap[tree[n, 0].label] = label
    stmts.join(label)
  of mnkCase:
    guardActive()
    # translate to a chain of ``If`` statements, as the target IL doesn't
    # support case statements ranges as labels
    let tmp = c.newTemp(tree[n, 0].typ)
    stmts.addStmt Asgn:
      bu.useLvalue tmp
      c.translateValue(env, tree, tree.child(n, 0), true, bu)

    var next = c.prc.newLabel()
    for b in tree.items(n, 1, ^1):
      let then = c.prc.request(tree[tree.last(b)].label)

      for it in tree.items(b, 0, ^2):
        stmts.join next
        next = c.prc.newLabel()
        if tree[it].kind == mnkRange:
          let other = c.prc.newLabel()
          stmts.addStmt Branch:
            bu.subTree Le:
              bu.add typeRef(c, env, tree[n, 0].typ)
              c.translateValue(env, tree, tree.child(it, 0), true, bu)
              bu.use tmp
            bu.goto(next)
            bu.goto(other)
          stmts.join other
          stmts.addStmt Branch:
            bu.subTree Le:
              bu.add typeRef(c, env, tree[n, 0].typ)
              bu.use tmp
              c.translateValue(env, tree, tree.child(it, 1), true, bu)
            bu.goto(next) # continue with the next check
            bu.goto(then) # jump to the body of the branch
        else:
          stmts.addStmt Branch:
            bu.subTree Eq:
              bu.add typeRef(c, env, tree[n, 0].typ)
              bu.use tmp
              c.translateValue(env, tree, it, true, bu)
            bu.goto(next)
            bu.goto(then)

      if tree[b].len == 1:
        # it's an 'else' branch
        stmts.join next
        stmts.goto then

    if tree[tree.last(n)].len != 1:
      # there's no 'else' branch
      stmts.join next
      stmts.addStmt Unreachable:
        discard

    c.prc.active = false
  of mnkExcept:
    var label: uint32
    if not c.prc.labelMap.pop(tree[n, 0].label, label):
      return

    let temp = c.newTemp(PointerType)
    stmts.addStmt Except:
      bu.add node(Immediate, label)
      bu.add temp.nodes
    if tree[n].len > 1:
      # it's not a catch-all branch. The exception's dynamic type needs to be
      # compared against the expected types
      let then = c.prc.newLabel()
      var els = c.prc.newLabel()

      let
        ex = c.newTemp(PointerType)
        excType = env.types.add(c.graph.getCompilerProc("Exception").typ)
        expr = buildExpr excType:
          bu.subTree Deref:
            bu.add typeRef(c, env, excType)
            bu.use ex

      stmts.putInto ex, Call:
        bu.add compilerProc(c, env, "nimBorrowCurrentException")

      for it in tree.items(n, 1, ^2):
        stmts.join(els)
        els = c.prc.newLabel()
        stmts.addStmt Branch:
          c.genOf(env, tree, expr, tree[it].typ, bu)
          bu.goto(els)
          bu.goto(then)

      stmts.join(els)
      # the exception needs to be re-raised if none of the types match
      stmts.addStmt Raise:
        bu.use temp
        c.genExit(tree, tree.last(n), bu)
      stmts.join(then)

    c.prc.active = true
  of mnkFinally:
    var label: uint32
    if c.prc.labelMap.pop(tree[n, 0].label, label):
      let temp = c.newTemp(PointerType)
      stmts.addStmt Except:
        bu.add node(Immediate, label)
        bu.add temp.nodes
      c.prc.active = true
  of mnkContinue:
    guardActive()
    stmts.addStmt Raise:
      bu.add node(IntVal, 0)
      c.genExit(tree, tree.child(n, 0), bu)
    c.prc.active = false
  of mnkRaise:
    guardActive()
    # NimSkull exceptions are managed separately; there's nothing to pass
    # along to ``Raise``
    stmts.addStmt Raise:
      bu.add node(IntVal, 0)
      c.genExit(tree, tree.child(n, 0), bu)
    c.prc.active = false
  of mnkEmit, mnkAsm:
    # XXX: ignore these statements for now
    warn(c, tree[n].info, "unsupported statement")
  else:
    unreachable()

proc genAll(env: var MirEnv, tree: MirTree, bu; c) =
  var n = NodePosition 0
  while ord(n) < tree.len:
    translateStmt(env, tree, n, bu, c)
    n = tree.sibling(n)

proc isFilled(t: seq[Node]): bool =
  t.len != 0

proc reset(c: var ProcContext) =
  c.localMap.clear()
  c.labelMap.clear()
  c.temps.shrink(0)
  c.params.shrink(0)
  c.indirectLocals.clear()
  c.sources.reset()

proc complete(c; env: MirEnv, typ: Node, prc: ProcContext, body: MirBody,
              content: seq[Node]): seq[Node] =
  ## Assembles the complete IL definition for a procedure. `typ` is a
  ## reference to the signature type, `prc` is the procedure's translation
  ## context, and `content` is the statement list that makes up the body.
  var bu = initBuilder[NodeKind](ProcDef)
  bu.add typ
  bu.subTree Params:
    for it in prc.params.items:
      bu.add node(Local, it)
  bu.subTree Locals:
    for id, it in body.locals.pairs:
      if env.types.canonical(it.typ) != VoidType:
        if id in prc.indirectLocals:
          bu.add typeRef(c, env, PointerType)
        else:
          bu.add typeRef(c, env, it.typ)

    for it in c.prc.temps.items:
      bu.add typeRef(c, env, it)

  bu.add content
  result = bu.finish()

proc translateProc(c; env: var MirEnv, procType: TypeId,
                   body: sink MirBody): seq[Node] =
  ## Translates the full body of a procedure (with signature `procType`) to
  ## a semantically equivalent IL ``ProcDef``, returning the latter.
  c.prc.reset()
  c.prc.sources = move body.source

  var bias = 0
  for id, it in body.locals.pairs:
    if env.types.canonical(it.typ) == VoidType:
      inc bias
    else:
      c.prc.localMap[id] = uint32(id.ord - bias)

  let procTypeDesc = env.types.headerFor(procType, Canonical)

  # gather the list of IL parameters
  for (i, typ, flags) in env.types.params(procTypeDesc):
    if env.types.canonical(typ) != VoidType:
      c.prc.params.add c.prc.localMap[LocalId(i + 1)]
      if pfByRef in flags:
        c.prc.indirectLocals.incl LocalId(i + 1)

  if procTypeDesc.kind == tkClosure:
    # register the environment parameter
    c.prc.params.add c.prc.localMap[LocalId(procTypeDesc.numParams() + 1)]

  c.prc.nextLabel = body.nextLabel.uint32
  c.prc.nextLocal = uint32(body.locals.nextId.ord - bias)
  c.prc.active = true

  # translate the body:
  let content = block:
    var bu = initBuilder[NodeKind](Stmts)
    genAll(env, body.code, bu, c)

    if c.prc.active:
      # a return statement is required if control-flow falls through at the
      # end
      bu.subTree Return:
        if body[LocalId 0].typ != VoidType:
          bu.subTree Copy:
            bu.add node(Local, c.prc.localMap[LocalId 0])

    bu.finish()

  let typ = c.genProcType(env, procType)
  c.complete(env, typ, c.prc, body, content)

proc replaceProcAst(config: ConfigRef, prc: PSym, with: PNode) =
  ## Replaces the ``PSym.ast`` of `prc` with the routine AST `with`,
  ## reparenting all symbols found in the body. This is crude, brittle, and
  ## best described as "don't do this" -- we rely on the patched-with
  ## procedure bodies to be simple enough for this to not cause any problems.
  assert with.kind in {nkProcDef, nkFuncDef}
  var map: Table[int, PSym]
  var prev = with[namePos].sym

  proc patch(n: PNode) =
    case n.kind
    of nkSym:
      if n.sym.owner == prev:
        map.withValue n.sym.id, it:
          n.sym = it[]
        do:
          # IDs for locals only need to be unique within their parent
          # procedure, so duplicating the ID here is fine
          let s = copySym(n.sym, n.sym.itemId)
          s.owner = prc # reparent
          map[s.id] = s
          n.sym = s

    of nkArgList, nkWithoutSons - {nkSym}:
      discard "nothing to do"
    of nkTypeSection, callableDefs:
      config.internalError(n.info, "too complex to patch")
    else:
      for it in n.items:
        patch(it)

  var n = copyTree(with)
  n[namePos] = newSymNode(prc)
  # don't patch the name
  for i in (namePos + 1)..<n.len:
    patch(n[i])

  prc.ast = n
  # the proc type also contains symbols; it needs to be updated too
  prc.typ = copyType(with[namePos].sym.typ, with[namePos].sym.typ.itemId, prc)
  patch(prc.typ.n)

proc processEvent(env: var MirEnv, bodies: var ProcMap,
                  partial: var Table[ProcedureId, Builder[NodeKind]],
                  graph: ModuleGraph,
                  c;
                  evt: sink BackendEvent) =
  case evt.kind
  of bekModule, bekConstant:
    discard "nothing to do"
  of bekDiscovered:
    case evt.entity.kind
    of mnkGlobal:
      c.globalsMap[evt.entity.global] =
        c.newGlobal(env, env.types.add(env[evt.entity.global].typ))
    of mnkConst:
      # constants are translated to IL globals too
      c.constMap[evt.entity.cnst] =
        c.newGlobal(env, env.types.add(env[evt.entity.cnst].typ))
    of mnkProc:
      let prc = env.procedures[evt.entity.prc]
      if sfImportc in prc.flags:
        # replace importc'ed procedures with their corresponding overrides
        let override = graph.getCompilerProc("hook_" & prc.extName)
        if override.isNil:
          graph.config.internalError(prc.info):
            "no override for importc'ed procedure found"
        else:
          replaceProcAst(graph.config, prc, override.ast)
          # copy all data that is relevant to code generation from the
          # override:
          prc.info = override.info
          prc.owner = override.owner
          prc.flags = override.flags
          prc.options = override.options
          prc.extname = override.extname
          prc.extFlags = override.extFlags
          prc.annex = override.annex
          prc.constraint = override.constraint

      if sfImportc in prc.flags:
        # the procedure is still imported, but now we know that it's deliberate
        var bu = initBuilder[NodeKind]()
        bu.subTree Import:
          bu.add c.genProcType(env, env.types.add(prc.typ))
          bu.add node(StringVal, c.lit.pack(prc.extname))
        bodies[c.registerProc(evt.entity.prc)] = finish(bu)
      else:
        # register the procedure on discovery, to keep the IL IDs in roughly
        # the same order as the MIR IDs. This is only relevant for
        # debuggability
        discard c.registerProc(evt.entity.prc)

    else:
      unreachable()
  of bekPartial:
    # a new procedure is created for each fragment, with a call to the new
    # procedure then being appended to the partial procedure. This is much
    # easier to implement than trying to append all fragments directly to the
    # partial procedure
    if evt.id notin partial:
      partial[evt.id] = initBuilder(Stmts)

    var body = evt.body
    apply(body, env) # apply the additional MIR passes

    let
      procType = env.types.add(evt.sym.typ)
      r = c.translateProc(env, procType, body)
    # important: do **not** inline `r`. The translateProc call may modify
    # nextProc, which would then lead to the wrong slot being assigned to
    bodies[c.nextProc] = r
    inc c.nextProc

    # add a call of the sub-procedure to the partial procedure:
    partial[evt.id].add @[node(Call, 1), node(Proc, c.nextProc-1)]
  of bekProcedure:
    var body = evt.body
    apply(body, env) # apply the additional MIR passes

    let procType = env.types.add(evt.sym.typ)
    bodies[c.registerProc(evt.id)] = c.translateProc(env, procType, body)
  of bekImported:
    # dynlib procedures are not supported
    c.graph.config.localReport(evt.sym.info,
      SemReport(kind: rsemUserError,
                str: "dynlib procedures are not supported"))

proc generateCodeForMain(c; env: var MirEnv; m: Module,
                         modules: ModuleList): (PSym, seq[Node]) =
  ## Generates the IL for the entry procedure, that is, the top-level procedure
  ## representing the whole program.

  # we use the compiler-provided main procedure generation here, but ignore
  # the body, as we're only interested in the symbol
  let prc = generateMainProcedure(c.graph, m.idgen, modules)

  # we cannot use the standard MIR translation, because:
  # * the ``process`` iterator is done already
  # * we need to inject additional IL code at the start of the body
  let body = generateCode(c.graph, env, prc, TranslationConfig(),
                          prc.ast[bodyPos])
  c.prc.reset()

  # manually setup the mapping for the result variable
  c.prc.localMap[LocalId(0)] = 0'u32

  var bu = initBuilder(Stmts)
  # make sure a global exists for all data underlying the constants:
  for cnst, id in c.constMap.pairs:
    let data = env.dataFor(cnst)
    if data notin c.dataMap:
      c.dataMap[data] = c.newGlobal(env, env.types.add(env[cnst].typ))

  # emit the initialization for all data globals:
  for cnst, id in c.dataMap.pairs:
    let typ = env[cnst][0].typ
    let dest = makeExpr typ:
      bu.subTree Deref:
        bu.add typeRef(c, env, typ)
        bu.subTree Copy:
          bu.add node(Global, id)

    c.genConst(env, env[cnst], NodePosition(0), dest, bu)

  # emit the initialization for constants. While not required by the
  # NimSkull specification, we give each constant its own unique location
  for cnst, id in c.constMap.pairs:
    bu.subTree NodeKind.Store:
      bu.add typeRef(c, env, env.types.add(env[cnst].typ))
      bu.subTree Copy:
        bu.add node(Global, id)
      bu.subTree Load:
        bu.add typeRef(c, env, env.types.add(env[cnst].typ))
        bu.subTree Copy:
          bu.add node(Global, c.dataMap[env.dataFor(cnst)])

  c.prc.active = true
  genAll(env, body.code, bu, c)
  bu.subTree Return:
    bu.subTree Copy:
      bu.add node(Local, 0)

  let typ = c.genProcType(env, env.types.add(prc.typ))
  result = (prc, c.complete(env, typ, c.prc, body, finish(bu)))

proc generateCode*(graph: ModuleGraph): PackedTree[NodeKind] =
  ## Generates the IL code for the full program represented by `graph` and
  ## returns the result as a single self-contained IL module.
  block:
    # the ``TFrame`` system type must not be treated as an imported type (as
    # those are not supported by skully), so we have to "correct" the type
    # prior to MIR processing
    let s = graph.systemModuleSym(graph.cache.getIdent("TFrame"))
    s.flags.excl sfImportc
    s.extFlags.excl exfNoDecl
    # recompute the size:
    s.typ.size = szUncomputedSize
    discard graph.config.getSize(s.typ)

  # --- run the MIR processing and translate the MIR code
  let config =
    BackendConfig(noImported: true, # prefer not using FFI procedures
                  tconfig: TranslationConfig(magicsToKeep: MagicsToKeep))

  var
    discovery: DiscoveryData
    procs: ProcMap
    partial: Table[ProcedureId, Builder[NodeKind]]

    mlist = graph.takeModuleList()
    c = Context(graph: graph)
    env = initMirEnv(graph)

  # discover and generate code for all alive procedures:
  for ac in process(graph, mlist, env, discovery, config):
    processEvent(env, procs, partial, graph, c, ac)

  for id, it in partial.mpairs:
    # complete the statement list:
    it.subTree Return: discard

    var bu = initBuilder(ProcDef)
    # all partial procedure have signature ``proc()``. The main module's init
    # procedure does too, therefore its type can be used here
    bu.add c.genProcType(env, env.types.add(mlist.mainModule().init.typ))
    bu.subTree Params: discard
    bu.subTree Locals: discard
    bu.add finish(it)
    procs[c.registerProc(id)] = finish(bu)

  # now that all live entities are known, emit the main procedure:
  block:
    let (id, body) = generateCodeForMain(c, env, mainModule(mlist), mlist)
    procs[c.registerProc(env.procedures.add(id))] = body

  # compute some statistics about the generated code:
  block:
    var
      num = 0
      count = 0

    for id, it in procs.pairs:
      if it.len > 0:
        num += it.len
        inc count

    echo "total: ", num, " average: ", (num / count)

  # assemble the final tree from the various fragments:
  var bu = initBuilder[NodeKind](NodeKind.Module)
  bu.subTree TypeDefs:
    for it in c.types.keys:
      bu.add it

  bu.subTree GlobalDefs:
    for it in c.globals.items:
      bu.subTree GlobalDef:
        bu.add node(UInt, 8)
        bu.add node(IntVal, c.lit.pack(it.address.int + AddressBias))

    # the stack starts after the globals' memory region
    c.globalsAddress = align(c.globalsAddress, 8)

    # define the globals storing the memory configuration:
    bu.subTree GlobalDef: # stack start
      bu.add node(UInt, 8)
      bu.add node(IntVal, c.lit.pack(c.globalsAddress.BiggestInt))
    bu.subTree GlobalDef: # stack size
      bu.add node(UInt, 8)
      bu.add node(IntVal, c.lit.pack(StackSize))
    bu.subTree GlobalDef: # total memory
      bu.add node(UInt, 8)
      bu.add node(IntVal, c.lit.pack(c.globalsAddress.BiggestInt + StackSize))

  bu.subTree ProcDefs:
    for id, it in procs.pairs:
      bu.add it

  # the exports:
  bu.subTree List:
    bu.subTree Export:
      bu.add Node(kind: StringVal, val: c.lit.pack("stack_start"))
      bu.add Node(kind: Global, val: c.globals.len.uint32)
    bu.subTree Export:
      bu.add Node(kind: StringVal, val: c.lit.pack("stack_size"))
      bu.add Node(kind: Global, val: c.globals.len.uint32 + 1)
    bu.subTree Export:
      bu.add Node(kind: StringVal, val: c.lit.pack("total_memory"))
      bu.add Node(kind: Global, val: c.globals.len.uint32 + 2)

  result = initTree[NodeKind](finish(bu), c.lit)
