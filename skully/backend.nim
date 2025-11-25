## Implements the CGIR-based code generator for Skully.

import
  std/[
    tables
  ],
  std/private/[
    containers
  ],
  compiler/front/[
    options,
    msgs
  ],
  compiler/sem/[
    modulelowering
  ],
  compiler/ast/[
    ast_types,
    idents,
    lineinfos,
    report_enums,
    reports_sem,
    types
  ],
  compiler/modules/[
    modulegraphs,
  ],
  compiler/backend/[
    cgbackend,
    cgir2
  ],
  compiler/ic/[
    bitabs
  ],
  passes/[
    builders,
    syntax,
    trees
  ]

import std/options as std_options

type
  Node = TreeNode[NodeKind]
  NodePos = cgir2.NodeIndex

  LabelId = distinct uint32

  ProcContext = object
    localMap: Table[StringId, uint32]
    labelMap: Table[uint32, LabelId]
    locals: seq[Node]
    nextLocal: uint32
    nextLabel: uint32

  Context = object
    graph: ModuleGraph
    lit: Literals
    ptrSize: int64

    typeCache: Table[StringId, uint32]
      ## cache for the IL types resulting from CGIR types
    types: OrderedTable[seq[Node], uint32]
      ## maps IL types to the associated ID (i.e., position in the typedefs
      ## tree). This is used for simple culling of structurally equal types
      ## XXX: this is incredibly inefficient. Not only does it allocate a lot
      ##      of small sequences, the ordered table also incurs additional
      ##      overhead. A table that allows storing the actual key data (i.e.,
      ##      the type tree, in this case) should be used instead

    procMap: Table[StringId, uint32]
      ## maps CGIR procedures to their corresponding IL procedure IDs
    globalsMap: Table[StringId, uint32]
      ## maps CGIR globals and constants to IL globals
    constMap: Table[StringId, uint32]
    dataMap: Table[Datum, uint32]
    strMap: Table[StringId, uint32]
      ## string ID -> IL global storing the character array
    globals: seq[tuple[typ: uint32, hasValue: bool, init: uint32]]
      ## the IL globals

    prc: ProcContext

  SizeAlignState = object
    ## Accumulator object for size/alignment computation.
    size: int64
    alignment: int16

  Expr = object
    nodes: seq[Node]
    typ {.requiresInit.}: NodePos

const
  StackSize = 1024 * 1024 # 1 MiB

using
  m: CgModule
  pos: NodePos
  c: var Context
  stmts: var Builder[NodeKind]
  bu: var Builder[NodeKind]

proc `==`(a, b: LabelId): bool {.borrow.}

func align(v: int64, to: int16): int64 {.inline.} =
  let mask = int64(to - 1)
  (v + mask) and not mask

proc isArray(m; typ: StringId): bool =
  m.tast[m.types[typ]].kind == cnkArrayTy

proc resolve(m; pos): NodePos =
  if m.tast[pos].kind == cnkType:
    m.types[m.tast[pos].val.StringId]
  else:
    pos

iterator items(ast: Ast, pos; first=0; last = ^1): NodePos =
  let len = ast.len(pos)
  var pos = ast.child(pos, first)
  for _ in first .. (len - int(last)):
    yield pos
    pos = ast.next(pos)

iterator pairs(ast: Ast, pos): (int, NodePos) =
  var it = ast.child(pos, 0)
  for i in 0..<ast.len(pos):
    yield (i, it)
    it = ast.next(it)

proc warn(c; loc: TLineInfo, msg: sink string) =
  ## Reports a warning pointing to `loc`.
  # the warning is not a user-provided one, but there's no other warning report
  # kind that fits, nor is it possible to introduce one without forking the
  # compiler
  c.graph.config.localReport(loc,
    SemReport(kind: rsemUserWarning, str: msg))

proc error(c; loc: TLineInfo, msg: sink string) {.noreturn.} =
  ## Reports a fatal error pointing to `loc`.
  # TODO: there's `rsemCustomError` in the compiler, which would be ideal,
  #       but it's not implemented properly at the time of writing
  c.graph.config.fatalReport(loc,
    SemReport(kind: rsemUserError, str: msg))

proc toLineInfo(c; m; info: uint32): TLineInfo =
  ## Converts `info` to the equivalent ``TLineInfo`` value.
  if info == 0:
    unknownLineInfo
  else:
    let loc = m.infos[info - 1]
    newLineInfo(c.graph.config,
      c.graph.config.findFile(m.get(loc.file)),
      loc.line.int,
      loc.column.int)

template node(k: NodeKind, v: uint32): Node =
  Node(kind: k, val: v)

template node(k: NodeKind): Node =
  Node(kind: k)

template addType(c: var Context, name, code: untyped): uint32 =
  ## Builds a type using `code`, returning the created type's ID.
  if true:
    var name = initBuilder[NodeKind]()
    code
    c.types.mgetOrPut(finish(name), c.types.len.uint32)
  else:
    unreachable()

proc newLabel(c: var ProcContext): LabelId =
  result = LabelId(c.nextLabel)
  inc c.nextLabel

proc newTemp(c: var ProcContext; typ: Node): Node =
  let id = c.locals.len
  c.locals.add typ
  result = node(Local, id.uint32)

proc pushLabel(c: var ProcContext, n: CgNode) =
  assert n.kind == cnkLabel
  if c.labelMap.mgetOrPut(n.val, LabelId(c.nextLabel)) == LabelId(c.nextLabel):
    inc c.nextLabel

proc registerLocal(c: var ProcContext, name: StringId, typ: Node) =
  c.localMap[name] = c.locals.len.uint32
  c.locals.add typ

proc getType(m; pos): NodePos =
  case m.ast[pos].kind
  of cnkExprs - {cnkCall, cnkNilLit}:
    m.types[m.ast[pos, 0].val.StringId]
  of cnkCall:
    # fetch the return type of the callee's proc type
    var callee = getType(m, m.ast.child(pos, 0))
    if m.tast[callee].kind == cnkPtrTy:
      callee = resolve(m, m.tast.child(callee, 0))
    m.tast.child(callee, 1)
  else:
    unreachable(m.ast[pos].kind)

proc initSizeAlign(): SizeAlignState =
  SizeAlignState(size: 0, alignment: 1)

proc computeSizeAlign(c; m; pos): (int64, int16)

proc addField(s: var SizeAlignState, c; m; pos): int64 =
  ## Updates the size and alignment to include the given field, returning the
  ## offset of the field.
  let (size, alignment) = computeSizeAlign(c, m, m.tast.child(pos, 0))
  var fixed = m.unpackInt(m.tast[pos, 1].val).int16
  if fixed == 0:
    fixed = alignment
  s.size = align(s.size, fixed) # add necessary padding
  result = s.size
  s.alignment = max(s.alignment, fixed)
  s.size += size

proc mergeField(s: var SizeAlignState, c; m; pos) =
  ## Updates the size and alignment to include the given field in a union.
  let (size, alignment) = computeSizeAlign(c, m, m.tast.child(pos, 0))
  var fixed = m.unpackInt(m.tast[pos, 1].val).int16
  if fixed == 0:
    fixed = alignment
  s.size = max(s.size, size)
  s.alignment = max(s.alignment, fixed)

proc finish(s: sink SizeAlignState): (int64, int16) =
  # pad the size so that its a multiple of the alignment
  (align(s.size, s.alignment), s.alignment)

proc opaqueToIL(c; m; pos): Node =
  ## Translates an opaque type to an IL type with the closest semantics, using
  ## a name-based best-effort approach.
  # assume LLP64 data model for 64-bit and ILP32 data model for 32-bit
  # architectures
  case m.get(m.tast[pos, 0].val.StringId)
  of "size_t":
    node(UInt, c.ptrSize.uint32)
  of "unsigned long long":
    node(UInt, 8)
  of "long long":
    node(Int, 8)
  of "unsigned long", "unsigned int":
    node(UInt, 4)
  of "long", "int":
    node(Int, 4)
  of "unsigned short":
    node(UInt, 2)
  of "short":
    node(Int, 2)
  of "unsigned char":
    node(UInt, 1)
  of "char":
    node(Int, 1)
  else:
    error(c, unknownLineInfo,
      "unsupported C type: " & m.get(m.tast[pos, 0].val.StringId))

proc computeSizeAlign(c; m; pos): (int64, int16) =
  ## Computes the size and alignment of the type at `pos`.
  case m.tast[pos].kind
  of cnkType:
    computeSizeAlign(c, m, m.types[m.tast[pos].val.StringId])
  of cnkCharTy, cnkBoolTy:
    (1'i64, 1'i16)
  of cnkIntTy, cnkUIntTy, cnkFloatTy:
    let size = m.unpackInt(m.tast[pos, 0].val)
    (size, int16(size))
  of cnkPtrTy:
    (c.ptrSize, int16(c.ptrSize))
  of cnkStructTy:
    var s = initSizeAlign()
    for it in items(m.tast, pos, 1):
      discard s.addField(c, m, it)
    s.finish()
  of cnkUnionTy:
    var s = initSizeAlign()
    for it in items(m.tast, pos, 1):
      s.mergeField(c, m, it)
    s.finish()
  of cnkArrayTy:
    let (size, align) = computeSizeAlign(c, m, m.tast.child(pos, 1))
    (size * m.unpackInt(m.tast[pos, 0].val), align)
  of cnkOpaqueTy:
    let n = opaqueToIL(c, m, pos)
    case n.kind
    of Ptr:
      (c.ptrSize.int64, c.ptrSize.int16)
    of Int, UInt, Float:
      (n.val.int64, n.val.int16)
    else:
      unreachable()
  else:
    unreachable()

proc typeToIL(c; m; typ: StringId): uint32
proc typeToIL(c; m; pos; bu)

proc typeRef(c; m; typ: StringId): Node =
  node(Type, typeToIL(c, m, typ))

proc typeRef(c; m; pos): Node =
  case m.tast[pos].kind
  of cnkType:
    node(Type, typeToIL(c, m, m.tast[pos].val.StringId))
  else:
    let id = c.addType bu:
      c.typeToIL(m, pos, bu)
    node(Type, id)

proc typeToIL(c; m; pos; bu) =
  proc inlineTypeToIL(c; m; pos; bu) =
    case m.tast[pos].kind
    of cnkUnionTy, cnkStructTy, cnkArrayTy, cnkProcTy:
      # aggregate and proc types cannot be inlined; use an identified type
      bu.add typeRef(c, m, pos)
    else:
      typeToIL(c, m, pos, bu)

  case m.tast[pos].kind
  of cnkType:
    bu.add typeRef(c, m, m.tast[pos].val.StringId)
  of cnkVoidTy:
    bu.subTree Void: discard
  of cnkBoolTy, cnkCharTy:
    bu.add node(UInt, 1)
  of cnkIntTy:
    bu.add node(Int, m.unpackUInt(m.tast[pos, 0].val).uint32)
  of cnkUIntTy:
    bu.add node(UInt, m.unpackUInt(m.tast[pos, 0].val).uint32)
  of cnkFloatTy:
    bu.add node(Float, m.unpackUInt(m.tast[pos, 0].val).uint32)
  of cnkPtrTy:
    bu.add node(Ptr)
  of cnkOpaqueTy:
    bu.add opaqueToIL(c, m, pos)
  of cnkArrayTy:
    let (size, alignment) = computeSizeAlign(c, m, pos)
    bu.subTree Array:
      bu.add node(Immediate, size.uint32)
      bu.add node(Immediate, alignment.uint32)
      bu.add node(Immediate, m.unpackUInt(m.tast[pos, 0].val).uint32)
      inlineTypeToIL(c, m, m.tast.child(pos, 1), bu)
  of cnkStructTy:
    let (size, alignment) = computeSizeAlign(c, m, pos)
    var s = SizeAlignState()
    bu.subTree Record:
      bu.add node(Immediate, size.uint32)
      bu.add node(Immediate, alignment.uint32)
      for it in items(m.tast, pos, 1):
        if m.unpackInt(m.tast[it, 3].val) != 0:
          warn(c, toLineInfo(c, m, m.tast[it].info),
            "bit fields are not supported and are ignored")
        let off = s.addField(c, m, it)
        bu.subTree Field:
          bu.add node(Immediate, off.uint32)
          inlineTypeToIL(c, m, m.tast.child(it, 0), bu)
  of cnkUnionTy:
    let (size, alignment) = computeSizeAlign(c, m, pos)
    bu.subTree Union:
      bu.add node(Immediate, size.uint32)
      bu.add node(Immediate, alignment.uint32)
      for it in items(m.tast, pos, 1):
        inlineTypeToIL(c, m, m.tast.child(it, 0), bu)
  of cnkProcTy:
    bu.subTree ProcTy:
      # ignore the calling convention
      for i in 1..<m.tast.len(pos):
        inlineTypeToIL(c, m, m.tast.child(pos, i), bu)
  of cnkVarargs:
    error(c, unknownLineInfo, "varargs are not supported")
  else:
    unreachable($m.tast[pos].kind)

proc typeToIL(c; m; typ: StringId): uint32 =
  ## Translates `typ`, adding it to the environment and returning its
  ## IL-level ID.
  c.typeCache.withValue typ, val:
    # already cached
    result = val[]
  do:
    # translate the type and cache it
    result = c.addType bu:
      c.typeToIL(m, m.types[typ], bu)
    c.typeCache[typ] = result

proc spawnGlobal(c; typ: uint32, data: string): uint32 =
  ## Spawns a new global variable with the given `typ` and the initial
  ## value represented by the byte string `data`.
  result = c.globals.len.uint32
  c.globals.add (typ, true, c.lit.pack(data))

proc spawnGlobal(c; typ: uint32): uint32 =
  ## Spawns a new global variable with the given `typ` and undefined initial
  ## value.
  result = c.globals.len.uint32
  c.globals.add (typ, false, 0'u32)

proc genStrLiteral(c; m; str: StringId): uint32 =
  ## Returns the ID for the global storing the raw character array for `str`,
  ## creating it first if hasn't been yet.
  c.strMap.withValue str, val:
    result = val[]
  do:
    # the character array for a literal string always includes the NUL
    # terminator
    var data = m.get(str)
    data.add "\0"

    let typ = c.addType bu:
      bu.subTree Array:
        bu.add node(Immediate, data.len.uint32) # length
        bu.add node(Immediate, 1) # alignment
        bu.add node(Immediate, data.len.uint32) # size
        bu.add node(UInt, 1)

    result = c.spawnGlobal(typ, data)
    c.strMap[str] = result

proc join(bu; label: LabelId) =
  bu.subTree Join:
    bu.add node(Immediate, label.uint32)

proc goto(bu; label: LabelId) =
  bu.subTree Goto:
    bu.add node(Immediate, label.uint32)

proc exitToIL(c; m; pos; bu) =
  case m.ast[pos].kind
  of cnkUnwind:
    bu.subTree Unwind:
      discard
  of cnkLabel:
    bu.goto c.prc.labelMap[m.ast[pos].val]
  else:
    unreachable()

template makeExpr(t: NodePos, code: untyped): Expr =
  if true:
    let x = t
    var bu {.inject.} = initBuilder[NodeKind]()
    code
    Expr(nodes: finish(bu), typ: x)
  else:
    unreachable()

proc use(bu; e: Expr) =
  bu.add e.nodes

proc exprToIL(c; m; pos; bu)

proc pathToIL(c; m; target: Expr, pos; num: int): Expr =
  proc step(c; m; target: Expr, pos; num: int): Expr =
    if num == 0:
      return target
    case m.tast[target.typ].kind
    of cnkArrayTy:
      let target = makeExpr resolve(m, m.tast.child(target.typ, 1)):
        bu.subTree At:
          bu.use target
          case m.ast[pos].kind
          of cnkInt:
            bu.add node(IntVal, c.lit.pack(m.unpackInt(m.ast[pos].val)))
          else:
            c.exprToIL(m, pos, bu)
      step(c, m, target, m.ast.next(pos), num - 1)
    of cnkStructTy, cnkUnionTy:
      let target = makeExpr resolve(m, m.tast.child(m.tast.child(target.typ, 1 + m.unpackInt(m.ast[pos].val)), 0)):
        bu.subTree Field:
          bu.use target
          bu.add node(Immediate, m.unpackUInt(m.ast[pos].val).uint32)
      step(c, m, target, m.ast.next(pos), num - 1)
    of cnkOpaqueTy:
      error(c, toLineInfo(c, m, m.ast[pos].info),
        "opaque type access is not supported")
    else:
      unreachable(m.tast[target.typ].kind)

  step(c, m, target, pos, num)

proc typeRefToIL(c; m; pos; bu) =
  bu.add typeRef(c, m, m.ast[pos].val.StringId)

proc nameToIL(c; m; pos): Node =
  case m.ast[pos].kind
  of cnkLocal:
    node(Local, c.prc.localMap[m.ast[pos].val.StringId])
  of cnkGlobal:
    node(Global, c.globalsMap[m.ast[pos].val.StringId])
  of cnkDatum:
    node(Global, c.dataMap[m.ast[pos].val.Datum])
  of cnkProc:
    node(Proc, c.procMap[m.ast[pos].val.StringId])
  of cnkUnknown:
    if m.ast[pos, 1].val.StringId in m.globals:
      node(Global, c.globalsMap[m.ast[pos, 1].val.StringId])
    elif m.ast[pos, 1].val.StringId in m.procs:
      node(Proc, c.procMap[m.ast[pos, 1].val.StringId])
    else:
      error(c, toLineInfo(c, m, m.ast[pos, 1].info), "")
  else:
    unreachable()

proc lvalueToIL(c; m; pos; bu) =
  case m.ast[pos].kind
  of cnkLocal, cnkGlobal, cnkUnknown:
    # may happen for the expression on the LHS of assignments
    bu.add nameToIL(c, m, pos)
  of cnkUse:
    # can only be a name reference
    bu.add nameToIL(c, m, m.ast.child(pos, 1))
  of cnkPath:
    let typ = m.getType(m.ast.child(pos, 1))
    let target =
      case m.tast[typ].kind
      of cnkPtrTy:
        makeExpr m.resolve(m.tast.child(typ, 0)):
          bu.subTree Deref:
            bu.add typeRef(c, m, m.tast.child(typ, 0))
            c.exprToIL(m, m.ast.child(pos, 1), bu)
      else:
        # the root must be an lvalue
        makeExpr m.resolve(typ):
          c.lvalueToIL(m, m.ast.child(pos, 1), bu)

    bu.use pathToIL(c, m, target, m.ast.child(pos, 2), m.ast.len(pos) - 2)
  else:
    unreachable()

proc magicToIL(c; m; pos; bu): bool =
  ## If possible, emits a custom implementation for the call at `pos` using
  ## built-in ops. Returns whether a custom implementation was emitted.
  if m.ast[pos, 0].kind == cnkUse and m.ast[m.ast.child(pos, 0), 1].kind == cnkProc:
    case m.get(m.ast[m.ast.child(pos, 0), 1].val.StringId)
    of "nimCopyMem":
      bu.subTree Blit:
        c.exprToIL(m, m.ast.child(pos, 1), bu)
        c.exprToIL(m, m.ast.child(pos, 2), bu)
        c.exprToIL(m, m.ast.child(pos, 3), bu)
      result = true
    of "nimZeroMem":
      bu.subTree Clear:
        c.exprToIL(m, m.ast.child(pos, 1), bu)
        c.exprToIL(m, m.ast.child(pos, 2), bu)
      result = true
    else:
      discard "nothing to do"

proc exprToIL(c; m; pos; bu) =
  template recurse(n: NodePos) =
    c.exprToIL(m, n, bu)

  proc conv(c; m; kind: NodeKind, pos; bu) =
    bu.subTree kind:
      c.typeRefToIL(m, m.ast.child(pos, 0), bu)
      bu.add typeRef(c, m, m.getType(m.ast.child(pos, 1)))
      recurse(m.ast.child(pos, 1))

  proc unaryOp(c; m; kind: NodeKind, pos; bu) =
    bu.subTree kind:
      c.typeRefToIL(m, m.ast.child(pos, 0), bu)
      recurse(m.ast.child(pos, 1))

  proc binOp(c; m; kind: NodeKind, pos; bu) =
    bu.subTree kind:
      c.typeRefToIL(m, m.ast.child(pos, 0), bu)
      recurse(m.ast.child(pos, 1))
      recurse(m.ast.child(pos, 2))

  proc cmpOp(c; m; kind: NodeKind, pos; bu) =
    bu.subTree kind:
      c.typeRefToIL(m, m.ast.child(pos, 1), bu)
      recurse(m.ast.child(pos, 2))
      recurse(m.ast.child(pos, 3))

  case m.ast[pos].kind
  of cnkUse:
    let n = nameToIL(c, m, m.ast.child(pos, 1))
    if n.kind == Proc:
      bu.add n
    else:
      bu.subTree Copy:
        bu.add n
  of cnkNilLit:
    bu.add node(Nil)
  of cnkValue:
    case m.ast[pos, 1].kind
    of cnkBool:
      bu.add node(IntVal, c.lit.pack(m.unpackInt(m.ast[pos, 1].val)))
    of cnkInt:
      bu.add node(IntVal, c.lit.pack(m.unpackInt(m.ast[pos, 1].val)))
    of cnkFloat:
      bu.add node(FloatVal, c.lit.pack(m.unpackFloat(m.ast[pos, 1].val)))
    of cnkString:
      # must be a pointer to nul-terminated-string
      bu.subTree Addr:
        bu.add node(Global, c.genStrLiteral(m, m.ast[pos, 1].val.StringId))
    else:
      unreachable(m.ast[pos, 1].kind)
  of cnkAddr:
    case m.ast[pos, 1].kind
    of cnkPath:
      bu.subTree Addr:
        c.lvalueToIL(m, m.ast.child(pos, 1), bu)
    of cnkLocal, cnkDatum, cnkGlobal, cnkUnknown, cnkProc:
      let n = nameToIL(c, m, m.ast.child(pos, 1))
      if n.kind == Proc:
        bu.add node(ProcVal, n.val)
      else:
        bu.subTree Addr:
          bu.add n
    else:
      unreachable()
  of cnkLoad:
    bu.subTree Load:
      c.typeRefToIL(m, m.ast.child(pos, 0), bu)
      recurse(m.ast.child(pos, 1))
  of cnkPath:
    # non-lvalue path expression
    bu.subTree Copy:
      c.lvalueToIL(m, pos, bu)
  of cnkConv:
    # implements numeric/pointer conversion as they work in C
    let dst = typeRef(c, m, m.ast[pos, 0].val.StringId)
    let src = typeRef(c, m, m.getType(m.ast.child(pos, 1)))
    if dst == src:
      # nothing to do
      c.exprToIL(m, m.ast.child(pos, 1), bu)
    elif dst.kind == Ptr or src.kind == Ptr:
      # TODO: perform a C-style conversion
      warn(c, toLineInfo(c, m, m.ast[pos].info), "missing conversion")
    elif dst.kind != src.kind and Float in {src.kind, dst.kind}:
      # conversion involving a float value
      conv(c, m, Conv, pos, bu)
    elif dst.kind == Float and src.kind == Float:
      let kind =
        if dst.val < src.val: Demote
        else:                 Promote
      conv(c, m, kind, pos, bu)
    else:
      # C-style integer conversion (try to preserve the numeric value when
      # converting to signed values; use module arithmetic for
      # unsigned targets)
      let kind =
        if dst.val == src.val:  Reinterp
        elif dst.val < src.val: Trunc
        elif src.kind == Int:   Sext
        else:                   Zext
      conv(c, m, kind, pos, bu)
  of cnkPromote: conv(c, m, Promote, pos, bu)
  of cnkDemote:  conv(c, m, Demote, pos, bu)
  of cnkUToF: conv(c, m, Conv, pos, bu)
  of cnkIToF: conv(c, m, Conv, pos, bu)
  of cnkFToI: conv(c, m, Conv, pos, bu)
  of cnkFToU: conv(c, m, Conv, pos, bu)
  of cnkTrunc: conv(c, m, Trunc, pos, bu)
  of cnkSext: conv(c, m, Sext, pos, bu)
  of cnkZext: conv(c, m, Zext, pos, bu)
  of cnkBitcast, cnkPtrCast:
    let dst = typeRef(c, m, m.ast[pos, 0].val.StringId)
    let src =
      if m.ast[pos, 1].kind == cnkNilLit:
        node(Type, c.addType(bu, bu.add(node(Ptr))))
      else:
        typeRef(c, m, m.getType(m.ast.child(pos, 1)))
    if dst == src:
      # nothing to do. May happen for casts involving bool or char types
      c.exprToIL(m, m.ast.child(pos, 1), bu)
    else:
      bu.subTree Reinterp:
        bu.add dst
        bu.add src
        c.exprToIL(m, m.ast.child(pos, 1), bu)
  of cnkCall:
    if not magicToIL(c, m, pos, bu):
      let ctyp = m.getType(m.ast.child(pos, 0))
      bu.subTree Call:
        if m.tast[ctyp].kind == cnkPtrTy:
          # it's an indirect call; use the indirect form
          bu.add typeRef(c, m, m.tast.child(ctyp, 0))
        recurse(m.ast.child(pos, 0))
        for it in m.ast.items(pos, 1):
          recurse(it)
  of cnkSizeof:
    let (size, _) = computeSizeAlign(c, m, m.types[m.ast[pos, 1].val.StringId])
    bu.add node(IntVal, c.lit.pack(size))
  of cnkAlignof:
    let (_, align) = computeSizeAlign(c, m, m.types[m.ast[pos, 1].val.StringId])
    bu.add node(IntVal, c.lit.pack(align))
  of cnkOffsetof:
    var tn = m.types[m.ast[pos, 1].val.StringId]
    var offset = 0'i64
    for it in m.ast.items(pos, 2):
      case m.tast[tn].kind
      of cnkStructTy:
        # sum the fields up until the selected one
        var s = SizeAlignState()
        var localOffset = 0'i64
        for i in 0..<m.unpackInt(m.ast[it].val):
          localOffset = s.addField(c, m, m.tast.child(tn, 1 + i))

        offset += localOffset
        tn = m.resolve(m.tast.child(m.tast.child(tn, 1 + m.unpackInt(m.ast[it].val)), 0))
      of cnkUnionTy:
        # the offset doesn't change
        tn = m.resolve(m.tast.child(m.tast.child(tn, 1 + m.unpackInt(m.ast[it].val)), 0))
      of cnkArrayTy:
        tn = m.resolve(m.tast.child(tn, 1))
        let (size, _) = computeSizeAlign(c, m, tn)
        offset += size * m.unpackInt(m.ast[pos].val)
      of cnkOpaqueTy:
        error(c, toLineInfo(c, m, m.ast[it].info),
          "accessing opaque types is not supported")
      else:
        unreachable()

    bu.add node(IntVal, c.lit.pack(offset))
  of cnkNeg: unaryOp(c, m, Neg, pos, bu)
  of cnkAdd: binOp(c, m, Add, pos, bu)
  of cnkSub: binOp(c, m, Sub, pos, bu)
  of cnkMul: binOp(c, m, Mul, pos, bu)
  of cnkDiv: binOp(c, m, Div, pos, bu)
  of cnkMod: binOp(c, m, Mod, pos, bu)
  of cnkNot:
    bu.subTree Not:
      recurse(m.ast.child(pos, 1))
  of cnkShl: binOp(c, m, Shl, pos, bu)
  of cnkShr: binOp(c, m, Shr, pos, bu)
  of cnkBitAnd: binOp(c, m, BitAnd, pos, bu)
  of cnkBitOr: binOp(c, m, BitOr, pos, bu)
  of cnkBitXor: binOp(c, m, BitXor, pos, bu)
  of cnkBitNot: unaryOp(c, m, BitNot, pos, bu)
  of cnkEq: cmpOp(c, m, Eq, pos, bu)
  of cnkLt: cmpOp(c, m, Lt, pos, bu)
  of cnkLe: cmpOp(c, m, Le, pos, bu)
  of cnkCheckedAdd, cnkCheckedSub, cnkCheckedMul:
    # TODO: implement these. While the L25 has checked arithmetic operations,
    #       they require the destination operand to be the name of a local,
    #       which is not the case for the CGIR destination operand, and
    #       emitting a temporary + assignment here is not easily doable
    unreachable()
  of AllNodes - cnkExprs:
    unreachable(m.ast[pos].kind)

proc constrToIL(c; m; pos; dest: Expr, bu) =
  ## Emits an IL assignment of `dest` to the expression at `pos`.
  case m.ast[pos].kind
  of cnkNilLit, cnkAddr, cnkUse, cnkBitCast, cnkPtrCast, cnkSizeof, cnkAlignof,
     cnkOffsetof:
    bu.subTree Asgn:
      bu.use dest
      c.exprToIL(m, pos, bu)
  of cnkValue:
    if isArray(m, m.ast[pos, 0].val.StringId):
      # special handling for character array initialization
      bu.subTree Blit:
        bu.subTree Addr:
          bu.use dest
        bu.subTree Addr:
          bu.add node(Global, c.genStrLiteral(m, m.ast[pos, 1].val.StringId))
        bu.add node(IntVal, c.lit.pack(m.get(m.ast[pos, 1].val.StringId).len))
      # the remaining slots are filled with zeros already
    else:
      bu.subTree Asgn:
        bu.use dest
        c.exprToIL(m, pos, bu)
  of cnkConstr:
    let isArray = isArray(m, m.ast[pos, 0].val.StringId)
    var i = 0
    for it in m.ast.items(pos, 1):
      let nDest =
        if isArray:
          makeExpr m.resolve(m.tast.child(dest.typ, 1)):
            bu.subTree At:
              bu.use dest
              bu.add node(IntVal, c.lit.pack(i))
        else:
          makeExpr m.resolve(m.tast.child(m.tast.child(dest.typ, 1 + i), 0)):
            bu.subTree Field:
              bu.use dest
              bu.add node(Immediate, c.lit.pack(i))
      c.constrToIL(m, it, nDest, bu)
      inc i
  of cnkRecConstr:
    for it in m.ast.items(pos, 1):
      let nDest = pathToIL(c, m, dest, m.ast.child(it, 0), m.ast.len(it) - 1)
      c.constrToIL(m, m.ast.last(it), nDest, bu)
  else:
    unreachable(m.ast[pos].kind)

proc isTrueLit(m; pos): bool =
  m.ast[pos].kind == cnkValue and
    m.ast[pos, 1].kind == cnkBool and
    m.unpackInt(m.ast[pos, 1].val) == 1

proc stmtToIL(c; m; pos; bu): bool =
  ## Translates the CGIR statement at `pos` to the IL, returning whether the
  ## statement returns.
  result = true # unless stated otherwise, the statement returns
  case m.ast[pos].kind
  of cnkDef:
    # ignore the register, noalias, and volatile flags
    let typ = m.types[m.ast[pos, 2].val.StringId]
    let (_, a) = computeSizeAlign(c, m, typ)
    if m.unpackInt(m.ast[pos, 0].val) > a or a > 8:
      warn(c, toLineInfo(c, m, m.ast[pos].info),
        "over-alignment of locals is not supported; the requirement is ignored")
    c.prc.registerLocal(m.ast[pos, 3].val.StringId, typeRef(c, m, typ))
  of cnkAsgn:
    bu.subTree Asgn:
      c.lvalueToIL(m, m.ast.child(pos, 0), bu)
      c.exprToIL(m, m.ast.child(pos, 1), bu)
  of cnkStore:
    bu.subTree NodeKind.Store:
      bu.add typeRef(c, m, m.tast.child(m.getType(m.ast.child(pos, 0)), 0))
      c.exprToIL(m, m.ast.child(pos, 0), bu)
      c.exprToIL(m, m.ast.child(pos, 1), bu)
  of cnkDrop:
    bu.subTree Drop:
      c.exprToIL(m, m.ast.child(pos, 0), bu)
  of cnkStmtList:
    for it in m.ast.items(pos):
      result = c.stmtToIL(m, it, bu)
  of cnkScope:
    result = c.stmtToIL(m, m.ast.child(pos, 0), bu)
  of cnkCall:
    c.exprToIL(m, pos, bu)
  of cnkCheckedCall:
    let ctyp = m.getType(m.ast.child(pos, 0))
    bu.subTree CheckedCall:
      if m.tast[ctyp].kind == cnkPtrTy:
        # it's an indirect call; use the indirect form
        bu.add typeRef(c, m, m.tast.child(ctyp, 0))
      c.exprToIL(m, m.ast.child(pos, 0), bu)
      for it in m.ast.items(pos, 1, ^2):
        c.exprToIL(m, it, bu)
      c.exitToIL(m, m.ast.last(pos), bu)
  of cnkCheckedCallAsgn:
    let ctyp = m.getType(m.ast.child(pos, 1))
    # the target IL only supports locals in the destination slot; go through
    # a temporary
    let tmp = c.prc.newTemp(typeRef(c, m, m.getType(m.ast.child(pos, 0))))
    bu.subTree CheckedCallAsgn:
      bu.add tmp
      if m.tast[ctyp].kind == cnkPtrTy:
        # it's an indirect call; use the indirect form
        bu.add typeRef(c, m, m.tast.child(ctyp, 0))
      c.exprToIL(m, m.ast.child(pos, 1), bu)
      for it in m.ast.items(pos, 2, ^2):
        c.exprToIL(m, it, bu)
      c.exitToIL(m, m.ast.last(pos), bu)
    bu.subTree Asgn:
      c.lvalueToIL(m, m.ast.child(pos, 0), bu)
      bu.subTree Copy:
        bu.add tmp
  of cnkWhile:
    let start = c.prc.newLabel()
    bu.join start
    if isTrueLit(m, m.ast.child(pos, 0)):
      if c.stmtToIL(m, m.ast.child(pos, 1), bu):
        bu.subTree Loop:
          bu.add node(Immediate, start.uint32)
      result = false # a 'while true' loop doesn't return
    else:
      let exit = c.prc.newLabel()
      let next = c.prc.newLabel()
      bu.subTree Branch:
        c.exprToIL(m, m.ast.child(pos, 0), bu)
        bu.goto exit
        bu.goto next
      bu.join next
      if c.stmtToIL(m, m.ast.child(pos, 1), bu):
        bu.subTree Loop:
          bu.add node(Immediate, start.uint32)

      bu.join exit
  of cnkIf:
    let then = c.prc.newLabel()
    let els = c.prc.newLabel()
    bu.subTree Branch:
      c.exprToIL(m, m.ast.child(pos, 0), bu)
      bu.goto els
      bu.goto then
    bu.join then
    result = c.stmtToIL(m, m.ast.child(pos, 1), bu)
    if m.ast.len(pos) == 3:
      if result:
        let after = c.prc.newLabel()
        bu.goto after
        bu.join els
        result = c.stmtToIL(m, m.ast.child(pos, 2), bu)
        bu.join after
      else:
        bu.join els
        result = c.stmtToIL(m, m.ast.child(pos, 2), bu)
    else:
      result = true # a single-branch if statement always returns
      bu.join els
  of cnkBreak:
    bu.goto c.prc.labelMap[m.ast[pos, 0].val]
    result = false
  of cnkUnreachable:
    bu.subTree Unreachable: discard
    result = false
  of cnkBlock:
    c.prc.pushLabel(m.ast[pos, 0])
    discard c.stmtToIL(m, m.ast.child(pos, 1), bu)
    bu.join c.prc.labelMap[m.ast[pos, 0].val]
  of cnkDispatch:
    # translate to a chain of ``If`` statements, as the target IL doesn't
    # support case statement ranges as labels
    let typ = m.getType(m.ast.child(pos, 0))
    let tmp = c.prc.newTemp(typeRef(c, m, typ))
    bu.subTree Asgn:
      bu.add tmp
      c.exprToIL(m, m.ast.child(pos, 0), bu)

    var after = none(LabelId)
    var next = none(LabelId)
    for b in m.ast.items(pos, 1):
      let then = c.prc.newLabel()
      for it in m.ast.items(b, 0, ^2):
        if next.isSome:
          bu.join next.unsafeGet
        next = some c.prc.newLabel()
        bu.subTree Branch:
          bu.subTree Eq:
            bu.add typeRef(c, m, typ)
            bu.subTree Copy:
              bu.add tmp
            c.exprToIL(m, it, bu)
          bu.goto(next.unsafeGet)
          bu.goto(then)

      if m.ast.len(b) == 1:
        # it's a catch-all target
        if next.isSome:
          bu.join next.unsafeGet
        next = none(LabelId)
        bu.goto then

      bu.join then
      if c.stmtToIL(m, m.ast.last(b), bu):
        if after.isNone:
          after = some c.prc.newLabel()
        bu.goto after.unsafeGet

    if next.isSome:
      # there's no catch-all target
      bu.join next.unsafeGet
      bu.subTree Unreachable:
        discard

    result = after.isSome
    if result:
      bu.join after.unsafeGet
  of cnkTry:
    c.prc.pushLabel(m.ast[pos, 0])
    discard c.stmtToIL(m, m.ast.child(pos, 1), bu)

    let typ = c.addType bu:
      bu.add node(Ptr)

    let tmp = c.prc.newTemp(node(Type, typ))
    bu.subTree Except:
      bu.add node(Immediate, uint32 c.prc.labelMap[m.ast[pos, 0].val])
      bu.add tmp
  of cnkRaise:
    bu.subTree Raise:
      bu.add node(Nil)
      c.exitToIL(m, m.ast.child(pos, 0), bu)
    result = false
  of cnkReturn:
    bu.subTree Return:
      if m.ast.len(pos) == 1:
        c.exprToIL(m, m.ast.child(pos, 0), bu)
    result = false
  of cnkEmit, cnkAsm:
    # XXX: ignore these statements for now
    warn(c, toLineInfo(c, m, m.ast[pos].info), "unsupported statement")
  of AllNodes - cnkStmts - cnkBlocks + {cnkTailCall}:
    unreachable(m.ast[pos].kind)

proc reset(c: var ProcContext) =
  c.localMap.clear()
  c.labelMap.clear()
  c.locals.shrink(0)
  c.nextLabel = 0
  c.nextLocal = 0

proc procToIL(c; m; pos): seq[Node] =
  ## Translates the CGIR procedure definition at `pos` to the IL.
  c.prc.reset()

  let params = m.ast.child(pos, 3)
  let tp = m.types[m.ast[pos, 1].val.StringId]
  for i, it in m.ast.pairs(params):
    c.prc.registerLocal(m.ast[it, 1].val.StringId,
      typeRef(c, m, m.tast.child(tp, i + 2)))

  # translate the body:
  let body = block:
    var bu = initBuilder[NodeKind](Stmts)
    discard stmtToIL(c, m, m.ast.child(pos, 4), bu)
    bu.finish()

  # wrap in a def:
  var bu = initBuilder[NodeKind](ProcDef)
  bu.add typeRef(c, m, m.ast[pos, 1].val.StringId)
  bu.subTree Params:
    for it in m.ast.items(params):
      bu.add node(Local, c.prc.localMap[m.ast[it, 1].val.StringId])
  bu.subTree Locals:
    for it in c.prc.locals.items:
      bu.add it

  bu.add body
  result = bu.finish()

proc generateMain(c; m): seq[Node] =
  ## Generates and returns the IL for the low-level entry procedure.
  let typ = c.addType bu:
    bu.subTree ProcTy:
      bu.add node(Int, 4)

  var bu = initBuilder(NodeKind.ProcDef)
  bu.add node(Type, typ)
  bu.subTree Params: discard
  bu.subTree Locals: discard
  bu.subTree Stmts:
    # emit the initialization for all anonymous constants:
    for datum, id in c.dataMap.pairs:
      let pos = m.data[datum]
      let dest = makeExpr m.types[m.ast[pos, 0].val.StringId]:
        bu.add node(Global, id)
      c.constrToIL(m, pos, dest, bu)

    # emit the initialization for all globals:
    for name, id in c.globalsMap.pairs:
      let pos = m.globals[name]
      case m.ast[pos].kind
      of cnkGlobalDef, cnkGlobalExp:
        if m.ast.len(pos) == 6:
          let dest = makeExpr m.types[m.ast[pos, 3].val.StringId]:
            bu.add node(Global, id)
          c.constrToIL(m, m.ast.child(pos, 5), dest, bu)
      of cnkGlobalImp:
        discard "nothing to do"
      else:
        unreachable()

    # emit a call to the high-level entry point:
    bu.subTree Return:
      bu.subTree Call:
        bu.add node(Proc, c.procMap[StringId m.strings.getKeyId("main")])
        bu.add node(IntVal, c.lit.pack(0))
        bu.add node(Nil)

  result = finish(bu)

proc generateCode*(graph: ModuleGraph, mlist: sink ModuleList): PackedTree[NodeKind] =
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

  let (m, _) = generateCode(graph, mlist, {capExceptions})

  var c = Context(graph: graph, ptrSize: graph.config.target.ptrSize)
  # fill the mapping tables:
  for name in m.procs.keys:
    c.procMap[name] = c.procMap.len.uint32
  for name, pos in m.globals.pairs:
    let id = c.spawnGlobal(typeToIL(c, m, m.ast[pos, 3].val.StringId))
    c.globalsMap[name] = id
  for datum, pos in m.data.pairs:
    let id = c.spawnGlobal(typeToIL(c, m, m.ast[pos, 0].val.StringId))
    c.dataMap[datum] = id

  # translate all procedures:
  var procs = newSeq[seq[Node]](c.procMap.len)
  for name, pos in m.procs.pairs:
    case m.ast[pos].kind
    of cnkProcDef, cnkProcExp:
      let body = procToIL(c, m, pos)
      procs[c.procMap[name]] = body
    of cnkProcImp:
      var bu = initBuilder(Import)
      bu.add typeRef(c, m, m.ast[pos, 1].val.StringId)
      bu.add node(StringVal, c.lit.pack(m.get(m.ast[pos, 2].val.StringId)))
      procs[c.procMap[name]] = finish(bu)
    else:
      unreachable()

  procs.add generateMain(c, m)

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
  var bu = initBuilder(NodeKind.Module)
  bu.subTree TypeDefs:
    for it in c.types.keys:
      bu.add it

  bu.subTree GlobalDefs:
    for it in c.globals.items:
      bu.subTree GlobalLoc:
        bu.add node(Type, it.typ)
        bu.subTree Data:
          bu.add node(Type, it.typ)
          if it.hasValue:
            bu.add node(StringVal, it.init)

    # define the globals storing the memory configuration:
    bu.subTree GlobalDef: # stack size
      bu.add node(UInt, 8)
      bu.add node(IntVal, c.lit.pack(StackSize))

  bu.subTree ProcDefs:
    for id, it in procs.pairs:
      bu.add it

  # the exports:
  bu.subTree List:
    bu.subTree Export:
      bu.add Node(kind: StringVal, val: c.lit.pack("stack_size"))
      bu.add Node(kind: Global, val: c.globals.len.uint32)

  result = initTree[NodeKind](finish(bu), c.lit)
