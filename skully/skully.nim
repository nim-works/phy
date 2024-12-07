import
  std/[importutils, monotimes, os, strtabs, packedsets, tables, times],
  compiler/front/[
    options,
    cli_reporter,
    optionsprocessor,
    condsyms,
    commands,
    cmdlinehelper,
    msgs
  ],
  compiler/sem/[
    passes,
    sem,
    modulelowering
  ],
  compiler/ast/[
    ast,
    ast_types,
    ast_query,
    idents,
    lineinfos
  ],
  compiler/modules/[
    modulegraphs,
    modules,
    magicsys
  ],
  compiler/utils/[
    containers,
    pathutils,
    platform
  ],
  compiler/backend/[
    backends,
    extccomp
  ],
  compiler/mir/[
    datatables,
    mirenv,
    mirtrees,
    mirtypes
  ],
  passes/[
    builders,
    changesets,
    debugutils,
    pass0,
    pass1,
    pass3,
    pass4,
    pass25,
    spec,
    trees
  ]

from compiler/mir/mirbodies import MirBody, `[]`

import vm/utils as vm_utils
import skully/passes as phy_passes

type
  Node = TreeNode[NodeKind]

  ProcContext = object
    localMap: Table[LocalId, uint32]
    labelMap: Table[LabelId, uint32]
    passByRef: PackedSet[LocalId]
      ## all parameters that use high-level pass-by-reference
    nextLabel: uint32
    nextLocal: uint32
    temps: seq[TypeId]
    active: bool

  PartialProc = object
    body: MirBody
    nodes: seq[Node]
    ctx: ProcContext

  Context = object
    graph: ModuleGraph
    lit: Literals

    typeMap: Table[TypeId, uint32]
      ## maps MIR type IDs to the ID of the cached IL type
    types: OrderedTable[seq[Node], uint32]
      ## maps IL types to the associated ID (i.e., position in the typedefs
      ## tree). This is used for simple culling of structurally equal types
      ## XXX: this is incredibly inefficient. Not only does it allocate a lot
      ##      of small sequences, the ordered table also incurs additional
      ##      overhead. A table that allows storing the actual key data (i.e.,
      ##      the type tree, in this case) should be used instead

    globalsMap: Table[GlobalId, uint32]
      ## maps MIR globals and constants to IL globals
    constMap: Table[ConstId, uint32]
    dataMap: Table[DataId, uint32]
    globals: seq[tuple[typ: TypeId, address: uint32]]
      ## the IL globals. address is the virtual address the underlying storage
      ## is located at
    globalsAddress: uint32
      ## the virtual address at where the next global should be located at

    prc: ProcContext

  Expr = object
    nodes: seq[Node]
    typ {.requiresInit.}: TypeId

  ProcMap = SeqMap[ProcedureId, seq[Node]]

const
  MagicsToKeep = {mNewSeq, mSetLengthSeq, mAppendSeqElem,
                  mEnumToStr, mDotDot, mEqCString, mAbsI}

using
  bu: var Builder[NodeKind]
  tree: MirTree
  n: NodePosition
  stmts: var Builder[NodeKind]
  c: var Context

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

iterator items(tree: MirTree, n: NodePosition, start: int, last: BackwardsIndex): NodePosition =
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
  bu.subTree Continue:
    bu.add node(Immediate, label)

proc join(bu; label: uint32) =
  bu.subTree Join:
    bu.add node(Immediate, label)

proc newGlobal(c; env: MirEnv, typ: TypeId): uint32 =
  let mask = uint32(env.types.headerFor(typ, Lowered).align - 1)
  # align the start address first:
  c.globalsAddress = (c.globalsAddress + mask) and not mask
  c.globals.add (typ, c.globalsAddress)
  # occupy the memory slot:
  c.globalsAddress += env.types.headerFor(typ, Lowered).size(env.types).uint32

  result = c.globals.high.uint32

proc newLabel(c: var ProcContext): uint32 =
  result = c.nextLabel
  inc c.nextLabel

proc newTemp(c; typ: TypeId): uint32 =
  assert typ != VoidType
  result = c.prc.nextLocal + c.prc.temps.len.uint32
  c.prc.temps.add typ

proc compilerProc(c; env: var MirEnv, name: string): Node =
  ## Requests the compilerproc with the given `name` and returns a reference
  ## to it.
  let p = c.graph.getCompilerProc(name)
  result = node(Proc, env.procedures.add(p).uint32)

proc genType(c; env: TypeEnv, typ: TypeId): uint32

proc typeRef(c; env: TypeEnv, typ: TypeId): Node =
  node(Type, c.genType(env, typ))

proc typeRef(c; env: MirEnv, typ: TypeId): Node =
  typeRef(c, env.types, typ)

proc genFlexArrayType(c; env: TypeEnv; typ: TypeId): uint32 =
  ## Returns the IL type ID of an array type with unknown length.
  var bu = initBuilder[NodeKind](Array)
  # size and number don't matter, but use the minimum possible value to be
  # safe
  bu.add node(Immediate, 1) # size
  bu.add node(Immediate, 0) # elements
  bu.add typeRef(c, env, typ)
  result = c.types.mgetOrPut(finish(bu), c.types.len.uint32)

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
    bu.subTree Continue:
      bu.add node(Immediate, c.prc.request(tree[n].label))
  else:
    unreachable()

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
    var pos = 0
    block search:
      for (f, recf) in env.fields(env.headerFor(typ, Lowered)):
        if env.headerFor(recf.typ, Canonical).kind == tkTaggedUnion:
          # a tagged union field counts as two: one for the tag, and one for
          # the union
          inc pos # skip the tag
          if findField(env, recf.typ, id, steps):
            if steps[^1] == 0: # is the field a tag field?
              # the tag is part of the embedder
              steps.del(steps.high)
              dec pos
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

    result = true
    steps.add uint32(pos)

  case env.types.headerFor(typ, Lowered).kind
  of tkRecord:
    let
      id = env.types.lookupField(typ, pos)
      (typ, depth) = findType(env.types, typ, pos)
    var steps: seq[uint32]
    # tagged unions are "inlined" in MIR record types, but not in IL types,
    # requiring additional field access
    doAssert findField(env.types, typ, id, steps)

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

proc genProcType(c; env: MirEnv, typ: TypeId): Node
proc gen(c; env: MirEnv, tree; n; wantsValue: bool): Expr

proc translateValue(c; env: MirEnv, tree: MirTree, n: NodePosition, wantValue: bool, bu) =
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
    # all globals are pointers, and thus a load is required
    bu.subTree (if wantValue: Load else: Deref):
      bu.add typeRef(c, env, tree[n].typ)
      bu.subTree Copy:
        bu.add node(Global, tree[n].global.uint32)
  of mnkNilLit:
    bu.add node(IntVal, 0)
  of mnkIntLit, mnkUIntLit:
    bu.add node(IntVal, c.lit.pack(env.getInt(tree[n].number)))
  of mnkFloatLit:
    bu.add node(FloatVal, c.lit.pack(env.getFloat(tree[n].number)))
  of mnkTemp, mnkLocal:
    wrapCopy:
      bu.add node(Local, c.prc.localMap[tree[n].local])
  of mnkParam:
    if tree[n].local in c.prc.passByRef:
      # needs a pointer indirection
      bu.subTree (if wantValue: Load else: Deref):
        bu.add typeRef(c, env, tree[n].typ)
        bu.subTree Copy:
          bu.add node(Local, c.prc.localMap[tree[n].local])
    else:
      wrapCopy:
        bu.add node(Local, c.prc.localMap[tree[n].local])
  of mnkAlias:
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
    bu.add node(ProcVal, tree[n].prc.uint32)
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
    recurse(tree.child(n, 0), wantValue)
  of mnkStrLit, mnkAstLit:
    unreachable()
  of AllNodeKinds - LvalueExprKinds - LiteralDataNodes - {mnkProcVal}:
    unreachable($tree[n].kind)

proc gen(c; env: MirEnv, tree; n; wantsValue: bool): Expr =
  var bu = initBuilder[NodeKind]()
  c.translateValue(env, tree, n, wantsValue, bu)
  result = makeExpr(finish(bu), tree[n].typ)
  assert result.nodes.len > 0

proc takeAddr(e: Expr, bu) =
  if e.nodes[0].kind == Deref:
    bu.add e.nodes.toOpenArray(2, e.nodes.high)
  else:
    bu.subTree Addr:
      bu.add e.nodes

proc genAsgn(dest: Expr, src: Expr; bu) =
  if dest.nodes.len == 0:
    bu.subTree Drop:
      bu.add src.nodes
  elif dest.nodes[0].kind == Deref:
    bu.subTree NodeKind.Store:
      bu.add dest.nodes[1]
      bu.add dest.nodes.toOpenArray(2, dest.nodes.high)
      bu.add src.nodes
  else:
    assert dest.nodes[0].kind != Load
    bu.subTree Asgn:
      bu.add dest.nodes
      bu.add src.nodes

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

proc genDefault(c; env: MirEnv; dest: Expr, typ: TypeId, bu) =
  let typ = env.types.canonical(typ)
  case env.types.headerFor(typ, Lowered).kind
  of tkBool, tkChar, tkInt, tkUInt, tkRef, tkPtr, tkVar, tkLent, tkPointer:
    genAsgn(dest, makeExpr(@[node(IntVal, 0)], typ), bu)
  of tkFloat:
    genAsgn(dest, makeExpr(@[node(FloatVal, c.lit.pack(0.0))], typ), bu)
  else:
    # TODO: implement
    discard

proc genField(c; env: MirEnv; tree; n; pos: int32, bu) =
  c.genField(env, c.gen(env, tree, n, false), pos, bu)

proc genOf(c; env: var MirEnv, tree; e: Expr, typ: TypeId; bu) =
  bu.subTree Call:
    bu.add compilerProc(c, env, "isObj")
    bu.subTree Copy:
      c.genField(env, e, -1, bu)
    # TODO: use the proper RTTI object. Unless we want to duplicate the RTTI
    #       code generation from ``cgen``, RTTI generation needs to be moved
    #       into ``mirgen`` first
    bu.add node(IntVal, 0)

proc genLength(c; env: var MirEnv; tree; n; dest: Expr, stmts) =
  let typ = env.types.canonical(tree[n].typ)
  case env.types.headerFor(typ, Canonical).kind
  of tkSeq, tkString:
    stmts.putInto dest, Copy:
      bu.subTree Field:
        c.translateValue(env, tree, n, false, bu)
        bu.add node(Immediate, 0)
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
    stmts.addStmt SelectBool:
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

proc use(bu; e: Expr) =
  case e.nodes[0].kind
  of Local, At, Field:
    bu.subTree Copy:
      bu.add e.nodes
  of Deref:
    bu.subTree Load:
      bu.add e.nodes[1]
      bu.add e.nodes.toOpenArray(2, e.nodes.high)
  else:
    bu.add e.nodes

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
  of mLtI, mLtF64, mLtEnum, mLtU, mLtCh:
    wrapAsgn Lt:
      bu.add typeRef(c, env, tree[tree.argument(n, 0)].typ)
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
  of mLeI, mLeF64, mLeEnum, mLeU, mLeCh:
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
      # TODO: implement
      discard
  of mIsNil:
    wrapAsgn Eq:
      let arg = tree.argument(n, 0)
      if env.types.headerFor(tree[arg].typ, Lowered).kind == tkProc:
        bu.add typeRef(c, env, tree[arg].typ)
        value(arg)
      else:
        # must be a closure
        bu.add typeRef(c, env, tree[arg].typ)
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(arg)
            bu.add node(Immediate, 0)
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
  of mDefault:
    c.genDefault(env, dest, tree[n].typ, stmts)
  of mMaxI, mMinI:
    let a = c.prc.newLabel()
    let b = c.prc.newLabel()
    let after = c.prc.newLabel()
    stmts.addStmt SelectBool:
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
    if env.types.headerFor(typ, Canonical).size(env.types) >= 0:
      wrapAsgn:
        bu.add node(IntVal, c.lit.pack(env.types.headerFor(typ, Canonical).size(env.types)))
    else:
      unreachable()
  of mAlignof:
    let typ = env.types.canonical(tree[tree.argument(n, 0)].typ)
    if env.types.headerFor(typ, Canonical).size(env.types) >= 0:
      wrapAsgn:
        bu.add node(IntVal, c.lit.pack(env.types.headerFor(typ, Canonical).align))
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
    wrapAsgn Eq:
      bu.add typeRef(c, env, env.types.sizeType)
      bu.subTree Load:
        bu.add typeRef(c, env, env.types.sizeType)
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(tree.argument(n, 0))
            bu.add node(Immediate, 0)

      bu.add node(IntVal, 0)
  of mCopyInternal:
    # copy the RTTI pointer
    stmts.addStmt Asgn:
      c.genField(env, tree, NodePosition tree.argument(n, 0), -1, bu)
      bu.subTree Copy:
        c.genField(env, tree, NodePosition tree.argument(n, 1), -1, bu)
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
    let tmp = makeExpr(@[node(Local, c.newTemp(env.types.sizeType))],
                       env.types.sizeType)
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
    # happens in practice in, meaning that the call expressions only ever have
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
      bu.subTree Call:
        bu.add compilerProc(c, env, "rawNewString")
        bu.add nodes # the length expression

    # emit the append calls:
    for (_, _, it) in tree.arguments(n):
      if tree[it].typ == CharType:
        stmts.addStmt Call:
          bu.add compilerProc(c, env, "appendChar")
          bu.subTree Addr:
            bu.add node(Local, temp)
      else:
        stmts.addStmt Call:
          bu.add compilerProc(c, env, "appendString")
          bu.subTree Addr:
            bu.add node(Local, temp)
          value(it)

    # assign to the destination:
    wrapAsgn Copy:
      bu.add node(Local, temp)
  of mParseBiggestFloat:
    wrapAsgn Call:
      bu.add compilerProc(c, env, "nimParseBiggestFloat")
      value(tree.argument(n, 0))
      value(tree.argument(n, 1))
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
    stmts.addStmt SelectBool:
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
    stmts.addStmt SelectBool:
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
          bu.add node(IntVal, c.lit.pack(1'i64 shl 63))
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
            bu.add node(Immediate, 0)
    of tkSeq:
      stmts.addStmt Call:
        bu.add compilerProc(c, env, "alignedDealloc")
        bu.subTree Copy:
          bu.subTree Field:
            lvalue(tree.argument(n, 0))
            bu.add node(Immediate, 0)
        bu.add node(IntVal, c.lit.pack(env.types.headerFor(typ, Canonical).align))
    else:
      unreachable("destroy was not lowered?")

    stmts.join els
  of mExit:
    # TODO: implement properly
    # the control-flow path needs to be marked as unreachable:
    stmts.addStmt Unreachable:
      discard
  of mEcho:
    # emit the array construction:
    let tmp = c.newTemp(tree[tree.argument(n, 0)].typ)
    for i in 1..<tree.numArgs(n):
      stmts.addStmt Asgn:
        bu.subTree At:
          bu.add node(Local, tmp)
          bu.add node(IntVal, c.lit.pack(i - 1))
        value(tree.argument(n, i))

    # emit the openArray construction:
    let
      prc = c.graph.getCompilerProc("echoBinSafe")
      oa  = c.newTemp(env.types.add(prc.typ[1]))

    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.add node(Local, oa)
        bu.add node(Immediate, 0)
      bu.subTree Addr:
        bu.add node(Local, tmp)
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.add node(Local, oa)
        bu.add node(Immediate, 1)
      bu.add node(IntVal, c.lit.pack(tree.numArgs(n) - 1))

    stmts.addStmt Call:
      bu.add compilerProc(c, env, "echoBinSafe")
      bu.subTree Copy:
        bu.add node(Local, oa)
  of mOf:
    wrapAsgn:
      c.genOf(env, tree,
              c.gen(env, tree, NodePosition tree.argument(n, 0), false),
              tree[tree.argument(n, 1)].typ,
              bu)
  else:
    # TODO: implement the remaining magics
    echo "missing magic: ", tree[n, 1].magic

proc translateExpr(c; env: var MirEnv, tree; n; dest: Expr, stmts) =
  template value(n: NodePosition) =
    c.translateValue(env, tree, n, true, bu)

  template lvalue(n: NodePosition) =
    mixin bu
    c.translateValue(env, tree, n, false, bu)

  template value(n: OpValue) =
    value(NodePosition n)

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
    if tree[n, 1].kind == mnkMagic:
      c.genMagic(env, tree, n, dest, stmts)
    else:
      let kind =
        if tree[n].kind == mnkCall:
          Call
        elif tree[n].typ == VoidType:
          CheckedCall
        else:
          CheckedCallAsgn

      proc genOperands(c; env: var MirEnv; tree; n; bu; stmts) {.nimcall.} =
        var isClosure: bool
        var typ: TypeId ## type of the callee

        if tree[n, 1].kind == mnkProc:
          # a static call
          typ = env.types.add(env[tree[n, 1].prc].typ)
          bu.add node(Proc, tree[n, 1].prc.uint32)
          isClosure = false
        else:
          # a dynamic call
          typ = env.types.canonical(tree[n, 1].typ)
          isClosure = env.types.headerFor(typ, Canonical).kind == tkClosure

          bu.add c.genProcType(env, typ)
          if isClosure:
            bu.subTree Copy:
              bu.subTree Field:
                lvalue(tree.child(n, 1))
                bu.add node(Immediate, 0)
          else:
            value(tree.child(n, 1))

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
                  bu.add node(Local, tmp)
                  value(it)
                bu.subTree Addr:
                  bu.add node(Local, tmp)
              else:
                takeAddr NodePosition(it)
            else:
              value(it)

          inc i

        if isClosure:
          # pass the environment to the procedure
          bu.subTree Copy:
            bu.subTree Field:
              lvalue(tree.child(n, 1))
              bu.add node(Immediate, 1)

        if tree[n].kind == mnkCheckedCall:
          c.genExit(tree, tree.last(n), bu)

      if kind == CheckedCallAsgn:
        # go through a temporary
        let tmp = c.newTemp(tree[n].typ)
        stmts.addStmt CheckedCallAsgn:
          bu.add node(Local, tmp)
          c.genOperands(env, tree, n, bu, stmts)

        wrapAsgn Copy:
          bu.add node(Local, tmp)
      elif tree[n].typ == VoidType:
        stmts.addStmt kind:
          c.genOperands(env, tree, n, bu, stmts)
      else:
        wrapAsgn kind:
          c.genOperands(env, tree, n, bu, stmts)
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
          bu.add dest.nodes
          bu.add node(Immediate, i.uint32)
        value(tree.last(it))
      inc i
  of mnkArrayConstr:
    c.genDefault(env, dest, tree[n].typ, stmts)

    var i = 0
    for it in tree.items(n, 0, ^1):
      stmts.addStmt Asgn:
        bu.subTree At:
          bu.add dest.nodes
          bu.add node(IntVal, c.lit.pack(i))
        value(tree.last(it))
      inc i
  of mnkSeqConstr:
    # emit the length initialization
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.add dest.nodes
        bu.add node(Immediate, 0)
      bu.add node(IntVal, c.lit.pack(tree.len(n)))

    # emit the payload initialization:
    stmts.addStmt Asgn:
      bu.subTree Field:
        bu.add dest.nodes
        bu.add node(Immediate, 1)
      bu.subTree Call:
        bu.add c.compilerProc(env, "newSeqPayload")
        bu.add node(IntVal, c.lit.pack(tree.len(n)))
        bu.add node(IntVal, c.lit.pack(0)) # TODO: size
        bu.add node(IntVal, c.lit.pack(0)) # TODO: align

    var i = 0
    for it in tree.items(n, 0, ^1):
      stmts.addStmt Asgn:
        bu.subTree At:
          bu.subTree Field:
            bu.subTree Deref:
              bu.add typeRef(c, env, payloadType(env.types, tree[n].typ))
              bu.subTree Copy:
                bu.subTree Field:
                  bu.add dest.nodes
                  bu.add node(Immediate, 1)
            bu.add node(Immediate, 1)
          bu.add node(IntVal, c.lit.pack(i))
        value(tree.child(it, 0))
      inc i

  of mnkToMutSlice, mnkToSlice:
    if tree[n].len == 1:
      let typ = env.types.canonical(tree[n, 0].typ)
      case env.types.headerFor(typ, Canonical).kind
      of tkCstring:
        # TODO: implement
        echo "unsupported: cstring slice"
      of tkArray:
        stmts.addStmt Asgn:
          bu.subTree Field:
            bu.add dest.nodes
            bu.add node(Immediate, 0)
          takeAddr tree.child(n, 0)
        stmts.addStmt Asgn:
          bu.subTree Field:
            bu.add dest.nodes
            bu.add node(Immediate, 1)
          bu.add node(IntVal, c.lit.pack(env.types.headerFor(typ, Canonical).arrayLen(env.types)))
      of tkSeq:
        stmts.addStmt Asgn:
          bu.subTree Field:
            bu.add dest.nodes
            bu.add node(Immediate, 0)
          # TODO: account for nil
          bu.subTree Addr:
            bu.subTree Field:
              bu.subTree Deref:
                bu.add typeRef(c, env, payloadType(env.types, tree[n, 0].typ))
                bu.subTree Copy:
                  bu.subTree Field:
                    lvalue(tree.child(n, 0))
                    bu.add node(Immediate, 1)
              bu.add node(Immediate, 1)
        stmts.addStmt Asgn:
          bu.subTree Field:
            bu.add dest.nodes
            bu.add node(Immediate, 1)
          bu.subTree Copy:
            bu.subTree Field:
              lvalue(tree.child(n, 0))
              bu.add node(Immediate, 0)
      of tkOpenArray:
        # TODO: implement
        echo "openArray slice support is missing"
      else:
        unreachable()
    else:
      # TODO: implement
      echo "toOpenArray implementation is missing"
  of mnkSetConstr:
    # TODO: implement
    echo "set constructors are not implemented"
  of mnkCast:
    let dst = env.types.canonical(tree[n].typ)
    let src = env.types.canonical(tree[n, 0].typ)
    if dst == src:
      discard "a no-op"
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
      let a = env.types.headerFor(dst, Lowered).size(env.types)
      let b = env.types.headerFor(src, Lowered).size(env.types)
      if a == b: # same size, only reinterpret
        wrapAsgn Reinterp:
          bu.add typeRef(c, env, dst)
          bu.add typeRef(c, env, src)
          value tree.child(n, 0)
      else:
        # TODO: needs to first reinterpret and then convert
        echo "missing cast implementation"
  else:
    unreachable()

proc translateStmt(env: var MirEnv, tree; n; stmts; c) =
  template guardActive() =
    if not c.prc.active:
      return

  # XXX: the "is active" tracking is currently necessary because local dead-
  #      code elimination in ``mirgen`` for closure iterators doesn't work
  #      properly

  case tree[n].kind
  of mnkAsgn, mnkSwitch, mnkDef, mnkDefCursor, mnkInit, mnkBind, mnkBindMut:
    guardActive()
    let dest = c.gen(env, tree, tree.child(n, 0), false)
    if tree[n, 1].kind != mnkNone:
      c.translateExpr(env, tree, tree.child(n, 1), dest, stmts)
    else:
      c.genDefault(env, dest, tree[n, 0].typ, stmts)
  of mnkVoid:
    guardActive()
    c.translateExpr(env, tree, tree.child(n, 0), Expr(typ: VoidType), stmts)
    if tree[n, 0].kind in {mnkCall, mnkCheckedCall}:
      # handle noreturn calls; they need to be followed by an Unreachable
      let callee = tree.callee(tree.child(n, 0))
      if tree[callee].kind == mnkProc and
         sfNoReturn in env[tree[callee].prc].flags:
        stmts.addStmt Unreachable:
          discard
        c.prc.active = false
  of mnkScope, mnkEndScope:
    discard
  of mnkLoop:
    guardActive()
    stmts.addStmt Loop:
      bu.add node(Immediate, c.prc.labelMap[tree[n, 0].label])
    c.prc.active = false
  of mnkIf:
    guardActive()
    let label = c.prc.newLabel()
    stmts.addStmt SelectBool:
      c.translateValue(env, tree, tree.child(n, 0), true, bu)
      c.genExit(tree, tree.child(n, 1), bu)
      bu.goto label
    stmts.join label
  of mnkEndStruct:
    var label: uint32
    # the EndStruct can mark the end of both an If or Except. Only those
    # marking the end of an If need to be turned into a join heres
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
    # translate to a chain of If statements
    let tmp = c.newTemp(tree[n, 0].typ)
    stmts.addStmt Asgn:
      bu.add node(Local, tmp.uint32)
      c.translateValue(env, tree, tree.child(n, 0), true, bu)

    var next = c.prc.newLabel()
    for b in tree.items(n, 1, ^1):
      let then = c.prc.request(tree[tree.last(b)].label)

      for it in tree.items(b, 0, ^2):
        stmts.join next
        next = c.prc.newLabel()
        if tree[it].kind == mnkRange:
          let other = c.prc.newLabel()
          stmts.addStmt SelectBool:
            bu.subTree Lt:
              bu.add typeRef(c, env, tree[n, 0].typ)
              bu.subTree Copy:
                bu.add node(Local, tmp.uint32)
              c.translateValue(env, tree, tree.child(it, 0), true, bu)
            bu.goto(next)
            bu.goto(other)
          stmts.join other
          stmts.addStmt SelectBool:
            bu.subTree Lt:
              bu.add typeRef(c, env, tree[n, 0].typ)
              c.translateValue(env, tree, tree.child(it, 0), true, bu)
              bu.subTree Copy:
                bu.add node(Local, tmp.uint32)
            bu.goto(next) # continue with the next check
            bu.goto(then) # jump to the body of the branch
        else:
          stmts.addStmt SelectBool:
            bu.subTree Eq:
              bu.add typeRef(c, env, tree[n, 0].typ)
              bu.subTree Copy:
                bu.add node(Local, tmp.uint32)
              c.translateValue(env, tree, it, true, bu)
            bu.goto(next)
            bu.goto(then)

      if tree[b].len == 1:
        # it's an 'else' branch
        stmts.join next
        stmts.goto then

    if tree[tree.last(n)].len != 1:
      # there's no else branch
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
      bu.add node(Local, temp)
    if tree[n].len > 1:
      # it's not a catch-all branch. The exception's dynamic type needs to be
      # compared against the expected types
      let then = c.prc.newLabel()
      var els = c.prc.newLabel()

      let
        ex = makeExpr(@[node(Local, c.newTemp(PointerType))], PointerType)
        excType = env.types.add(c.graph.getCompilerProc("Exception").typ)
        expr = buildExpr excType:
          bu.subTree Deref:
            bu.add typeRef(c, env, excType)
            bu.subTree Copy:
              bu.add ex.nodes

      stmts.putInto ex, Call:
        bu.add compilerProc(c, env, "nimBorrowCurrentException")

      for it in tree.items(n, 1, ^2):
        stmts.join(els)
        els = c.prc.newLabel()
        stmts.addStmt SelectBool:
          c.genOf(env, tree, expr, tree[it].typ, bu)
          bu.goto(els)
          bu.goto(then)

      stmts.join(els)
      # the exception needs to be re-raised if none of the types match
      stmts.addStmt Raise:
        bu.subTree Copy:
          bu.add node(Local, temp)
        c.genExit(tree, tree.last(n), bu)
      stmts.join(then)

    c.prc.active = true
  of mnkFinally:
    var label: uint32
    if c.prc.labelMap.pop(tree[n, 0].label, label):
      let temp = c.newTemp(PointerType)
      stmts.addStmt Except:
        bu.add node(Immediate, label)
        bu.add node(Local, temp)
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
    echo "unsupported statement: ", tree[n].kind
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

proc complete(c; env: MirEnv, typ: Node, prc: ProcContext, body: MirBody,
              content: seq[Node]): seq[Node] =
  ## Assembles the complete IL definition for a procedure. `typ` is a
  ## reference to the signature type, `prc` is the procedure's translation
  ## context, and `content` is the statement list that makes up the body.
  var bu = initBuilder[NodeKind](ProcDef)
  bu.add typ
  bu.subTree Locals:
    for id, it in body.locals.pairs:
      if env.types.canonical(it.typ) != VoidType:
        if id in prc.passByRef:
          bu.add typeRef(c, env, PointerType)
        else:
          bu.add typeRef(c, env, it.typ)

    for it in c.prc.temps.items:
      bu.add typeRef(c, env, it)

  bu.add content
  result = bu.finish()

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
          # IDs for locals only need to be unique within their parent procedure,
          # so duplicating the ID here is fine
          let s = copySym(n.sym, n.sym.itemId)
          s.owner = prc # reparent
          map[s.id] = s
          n.sym = s

    of nkWithoutSons - {nkSym}:
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

proc processEvent(env: var MirEnv, bodies: var ProcMap, partial: var Table[ProcedureId, PartialProc], graph: ModuleGraph, c; evt: sink BackendEvent) =
  case evt.kind
  of bekDiscovered:
    case evt.entity.kind
    of mnkGlobal:
      c.globalsMap[evt.entity.global] = c.newGlobal(env, evt.entity.typ)
    of mnkConst:
      # constants are translated to IL globals too
      c.constMap[evt.entity.cnst] = c.newGlobal(env, evt.entity.typ)
    of mnkProc:
      let prc = env.procedures[evt.entity.prc]
      if sfImportc in prc.flags:
        # replace importc'ed procedures with their corresponding overrides
        let override = graph.getCompilerProc("hook_" & prc.name.s)
        if override.isNil:
          graph.config.internalError(prc.info):
            "no override for importc'ed procedure found"
        else:
          replaceProcAst(graph.config, prc, override.ast)
          # the procedure is no longer an FFI procedure; update the flags
          prc.flags.excl sfImportc
          prc.extFlags.excl exfDynamicLib
          prc.extFlags.excl exfNoDecl

    else:
      unreachable()
  of bekPartial:
    if evt.id notin partial:
      # XXX: an empty body is temporarily used in order to produced code that
      #      passes ``pass25``
      partial[evt.id] = PartialProc(nodes: @[node(Stmts, 1), node(Return, 0)])

    # TODO: implement the rest
  of bekProcedure:
    var body = evt.body
    apply(body, env) # apply the additional MIR passes

    c.prc.reset()

    var bias = 0
    for id, it in body.locals.pairs:
      if env.types.canonical(it.typ) == VoidType:
        inc bias
      else:
        c.prc.localMap[id] = uint32(id.ord - bias)

    let procType = env.types.add(evt.sym.typ)
    # gather the parameters that use pass-by-reference
    c.prc.passByRef.clear()
    for (i, _, flags) in env.types.params(env.types.headerFor(procType, Canonical)):
      if pfByRef in flags:
        c.prc.passByRef.incl LocalId(i + 1)

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
    bodies[evt.id] = c.complete(env, typ, c.prc, body, content)
  else:
    discard

proc translateProcType(c; env: TypeEnv, id: TypeId, bu) =
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

    if desc.callConv(env) == ccClosure:
      bu.add typeRef(c, env, PointerType)

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
      bu.add node(Immediate, desc.arrayLen(env).uint32)
      bu.add typeRef(c, env, desc.elem())
  of tkUncheckedArray:
    bu.subTree Array:
      bu.add node(Immediate, 0)
      bu.add node(Immediate, 1)
      bu.add typeRef(c, env, desc.elem())
  of tkRecord, tkUnion:
    let size =
      if desc.size(env) >= 0:
        desc.size(env)
      elif env[id] != nil and
           env[id].skipTypes(abstractVar).kind == tyOpenArray:
        # the size for openArrays is never filled in correctly; we have to
        # manually correct it here
        c.graph.config.target.ptrSize * 2
      else:
        szUnknownSize

    assert size >= 0
    bu.subTree Record:
      bu.add node(Immediate, size.uint32)

      if desc.kind == tkRecord and desc.base(env) != VoidType:
        # the inherited-from type is added as the first field
        bu.subTree Field:
          bu.add node(Immediate, 0)
          bu.add typeRef(c, env, desc.base(env))

      for f, recf in env.fields(desc):
        privateAccess(RecField)
        if env.headerFor(recf.typ, Canonical).kind == tkTaggedUnion:
          # the tag field is inlined into the embedder. This is simpler,
          # as it removes having to use another intermediate type
          let tag = env[env.lookupField(recf.typ, 0)].typ
          bu.subTree Field:
            bu.add node(Immediate, recf.offset.uint32)
            bu.add typeRef(c, env, tag)

          # XXX: all field offsets within the tagged union are relative to the
          #      start of the embedding record, and thus the union has to be
          #      placed at offset 0. This results in correct code generation,
          #      but it will cause issues as soon as the passes responsible for
          #      lowering records start to expect sane input
          bu.subTree Field:
            bu.add node(Immediate, 0)
            bu.add typeRef(c, env, recf.typ)
        else:
          bu.subTree Field:
            bu.add node(Immediate, recf.offset.uint32)
            bu.add typeRef(c, env, recf.typ)
  of tkImported:
    # TODO: imported types need to be handled differently. Either the target
    #       IL needs to support them, or they have to treated as their
    #       "underlying" type for now
    bu.subTree Record:
      bu.add node(Immediate, 0)
      bu.subTree Field:
        bu.add node(Immediate, 0)
        bu.add node(Type, CharType.uint32)
  of tkTaggedUnion:
    # only generate the union part, the tag field is inlined into the embedder
    bu.subTree Record:
      # TODO: properly compute the size. It's not stored in the MIR type header
      bu.add node(Immediate, 0)
      for f, recf in env.fields(desc, 1):
        bu.subTree Field:
          bu.add node(Immediate, 0)
          bu.add typeRef(c, env, recf.typ)
  of tkProc, tkPtr, tkRef, tkVar, tkLent, tkCstring:
    c.translate(env, PointerType, bu)
  else:
    unreachable($desc.kind)

proc genProcType(c; env: MirEnv, typ: TypeId): Node =
  let typ = env.types.canonical(typ)
  assert env.types.headerFor(typ, Canonical).kind in {tkProc, tkClosure}

  # XXX: the type is currently not cached
  var bu = initBuilder[NodeKind]()
  c.translateProcType(env.types, typ, bu)
  node(Type, c.types.mgetOrPut(finish(bu), c.types.len.uint32))

proc genType(c; env: TypeEnv, typ: TypeId): uint32 =
  let typ = env.canonical(typ)
  c.typeMap.withValue typ, val:
    # already cached
    result = val[]
  do:
    # translate the type and cache it
    var bu = initBuilder[NodeKind]()
    c.translate(env, typ, bu)
    result = c.types.mgetOrPut(finish(bu), c.types.len.uint32)
    c.typeMap[typ] = result

template measure(name: string, body: untyped) =
  let a = getMonoTime()
  body
  echo name, " took: ", inMilliseconds(getMonoTime() - a)

proc findPatchFile(config: ConfigRef, file: string): FileIndex =
  var patchDir = getAppDir()
  # search for the directory that contains the patch modules
  if dirExists(patchDir / ".." / "skully" / "patch"):
    patchDir = patchDir / ".." / "skully" / "patch"
  elif dirExists(patchDir / "patch"):
    patchDir = patchDir / "patch"
  else:
    # give up
    raise ValueError.newException("cannot find patch directory")

  var known: bool
  result = config.fileInfoIdx(AbsoluteFile(patchDir / file), known)

proc replaceModule(config: ConfigRef, name: string, with: string) =
  var known: bool
  # this is a horrible hack, but it's the most simple and straightforward
  # solution to replacing modules at compile time not requiring modifying
  # the compiler. We register the real file and then replace its ``FileInfo``
  # with that of the module we want to replace it with
  let
    idx = config.fileInfoIdx(findModule(config, name, ""), known)
    other = findPatchFile(config, with)
  config.m.fileInfos[ord idx] = config.m.fileInfos[ord other]

proc compile(graph: ModuleGraph) =
  # --- run the semantic pass for the project
  registerPass graph, semPass
  registerPass graph, collectPass
  compileProject(graph, graph.config.projectMainIdx)

  block:
    # the ``TFrame`` system type must not be treated as an imported type (as
    # those are not supported by skully), so we have to "correct" the type
    # prior to the MIR processing
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
    procs: SeqMap[ProcedureId, seq[Node]]
    partial: Table[ProcedureId, PartialProc]

    mlist = graph.takeModuleList()
    c = Context(graph: graph)
    env = initMirEnv(graph)

  # discover and generate code for all alive procedures:
  for ac in process(graph, mlist, env, discovery, config):
    processEvent(env, procs, partial, graph, c, ac)

  for id, it in partial.mpairs:
    # all partial procedure have signature ``proc()``. The main procedure does
    # too, therefore its type can be used here
    let typ = c.genProcType(env, env.types.add(mlist.mainModule().init.typ))
    procs[id] = c.complete(env, typ, it.ctx, it.body, it.nodes)

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

  # TODO: generate the main procedure, which is responsible for initializing
  #       the globals/constants/data, initializing the allocator, and calling
  #       the main module's procedure

  # assemble the final tree from the various fragments:
  var bu = initBuilder[NodeKind](NodeKind.Module)
  bu.subTree TypeDefs:
    for it in c.types.keys:
      bu.add it

  bu.subTree GlobalDefs:
    for it in c.globals.items:
      bu.add node(IntVal, c.lit.pack(it.address.int))

  bu.subTree ProcDefs:
    for id, it in procs.pairs:
      bu.add it

  var tree = initTree[NodeKind](finish(bu), c.lit)
  measure "pass25": tree = tree.apply(pass25.lower(tree))
  measure "pass4": tree = tree.apply(pass4.lower(tree))
  measure "pass3": tree = tree.apply(pass3.lower(tree, 8))
  measure "pass1": tree = tree.apply(pass1.lower(tree, 8))

proc main(args: openArray[string]) =
  let config = newConfigRef(cli_reporter.reportHook)
  config.writelnHook = proc(r: ConfigRef, output: string, flags: MsgFlags) =
    stdout.writeLine(output)
  config.writeHook = proc(r: ConfigRef, output: string, flags: MsgFlags) =
    stdout.write(output)

  let
    ids   = newIdentCache()
    graph = newModuleGraph(ids, config)

  # set up a working compiler environment:
  processCmdLine(passCmd1, [], config)
  config.setFromProjectName(args[^1])
  discard loadConfigs(DefaultConfig, ids, config)
  extccomp.initVars(config)
  processCmdLine(passCmd2, [], config)

  config.setFromProjectName(args[^1])
  wantMainModule(config)

  # use the "any" OS in order to disable most platform-specific code
  config.target.setTarget(osAny, cpuAmd64)

  config.setDefaultLibpath()
  config.searchPathsAdd config.libpath
  defineSymbol(config, "c")
  config.exc = excGoto
  config.backend = backendC
  initDefines(config.symbols)

  # the maximum heap size is fixed at compile-time, with the possibility to
  # override the default value
  if not isDefined(config, "StandaloneHeapSize"):
    defineSymbol(config, "StandaloneHeapSize", $(1024 * 1024 * 100)) # 100 MiB

  # replace some system modules:
  replaceModule(config, "pure/os", "os.nim")

  # add the overrides module as an implicit import, so that the hook
  # procedures part of it are added to the compilation
  config.implicitImportsAdd:
    config[findPatchFile(config, "overrides.nim")].fullPath.string

  # disable various C and platform specific code, in order to reduce the
  # amount of patching that's needed
  defineSymbol(config, "noSignalHandler") # disable default signal handlers
  defineSymbol(config, "nimNoLibc")
  defineSymbol(config, "nimEmulateOverflowChecks")
  defineSymbol(config, "nimPreviewFloatRoundtrip")

  config.astDiagToLegacyReport = cli_reporter.legacyReportBridge
  # XXX: only arc is support at the moment
  discard processSwitch("gc", "arc", passCmd2, config)

  # now compile the input module:
  compile(graph)

main(getExecArgs())
