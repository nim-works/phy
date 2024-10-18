## Implements the translation/lowering of L? code into the asm.js JavaScript
## subset.

import
  std/tables,
  passes/[
    trees,
    spec
  ],
  vm/[
    utils
  ]

type
  TypeId = distinct int

  ProcBucket = object
    ## Procedures are sorted into buckets, based on their type.
    start: int
    elems: seq[int32]

  Tables = object
    procMap: seq[tuple[bucket, rel: int]]
    bucketMap: Table[TypeId, int] ## proc type ID -> bucket index
    buckets: seq[ProcBucket]

  GraphNode = object
    ## A node in a control-flow graph. Corresponds to a continuation.
    isLoop: bool
      ## whether the node has a loop exit
    exits: seq[int32]
      ## all relevant outgoing edges
    firstExit: int
      ## the node with the lowest index jumping to this node

    isTarget: bool
      ## whether the node is targeted by a jump
    labels: seq[tuple[isLoop: bool, val: int]]

  PassCtx = object
    # inputs:
    types: NodeIndex

    # per-procedure state:
    locals: NodeIndex
    returnType: JsType
    tables: ptr Tables
    usesSp: bool
    current: int
      ## index of the current continuation
    nodes: seq[GraphNode]

  Formatter = object
    buf: string
    indent: int
    first: bool

  JsType = enum
    ## Corresponds to the asm.js types.
    jsVoid
    jsSigned
    jsUnsigned
    jsFloat
    jsDouble
    jsInt
    jsFixnum
    jsIntish
    jsFloatish

    jsUnknown

  TypeInfo = object
    kind: range[jsSigned..jsDouble]
    size: int

# shorten some common parameter definitions:
using
  c: PassCtx
  tree: PackedTree[NodeKind]
  f: var Formatter

proc `==`(a, b: TypeId): bool {.borrow.}

proc write(f: var Formatter, str: string) =
  if f.first:
    for i in 0..<f.indent * 2:
      f.buf.add ' '
    f.first = false
  f.buf.add str

proc writeLine(f: var Formatter, str: string) =
  if f.first:
    for i in 0..<f.indent * 2:
      f.buf.add ' '
    f.first = false
  f.buf.add str
  f.buf.add '\n'
  f.first = true

func imm(n: TreeNode[NodeKind]): int32 {.inline.} =
  assert n.kind == Immediate
  cast[int32](n.val)

func id(n: TreeNode[NodeKind]): int32 {.inline.} =
  assert n.kind in {Local, Global, Proc, ProcVal}
  cast[int32](n.val)

func typ(n: TreeNode[NodeKind]): TypeId {.inline.} =
  assert n.kind == Type
  TypeId(n.val)

proc parseType(tree; at: NodeIndex): TypeInfo =
  case tree[at].kind
  of Int:   TypeInfo(kind: jsSigned, size: tree[at, 0].imm)
  of UInt:  TypeInfo(kind: jsUnsigned, size: tree[at, 0].imm)
  of Float:
    case tree[at, 0].imm
    of 4: TypeInfo(kind: jsFloat, size: 4)
    of 8: TypeInfo(kind: jsDouble, size: 8)
    else: unreachable()
  else:     unreachable()

proc parseType(tree; types: NodeIndex, id: TypeId): TypeInfo =
  parseType(tree, tree.child(types, int(id)))

proc conv(f: var Formatter, typ: JsType, val: string) =
  case typ
  of jsSigned, jsInt:
    f.write val & "|0"
  of jsUnsigned:
    f.write val & ">>>0"
  of jsFloat:
    f.write "fround(" & val & ")"
  of jsDouble:
    f.write "+" & val
  else:
    unreachable()

proc genExpr(c; f; tree; val: NodeIndex): JsType

proc isSubtype(a, b: JsType): bool =
  ## Whether `b` is a sub-type of `a`.
  case a
  of jsFloatish:
    b in {jsFloat, jsFloatish}
  of jsFloat:
    b == jsFloat
  of jsDouble:
    b == jsDouble
  of jsInt:
    b in {jsInt, jsSigned, jsUnsigned, jsFixnum}
  of jsIntish:
    b in {jsIntish, jsInt, jsSigned, jsUnsigned, jsFixnum}
  of jsUnsigned:
    b in {jsUnsigned, jsFixnum}
  of jsSigned:
    b in {jsSigned, jsFixnum}
  else:
    false

proc genExpr(c; f; tree; val: NodeIndex, expect: JsType; force = false) =
  var start = f.buf.len
  let typ = c.genExpr(f, tree, val)
  # calls always require a coercion
  if not isSubtype(expect, typ) or tree[val].kind == Call or force:
    case expect
    of jsInt, jsSigned:
      f.buf.insert("(", start)
      f.write "|0)"
    of jsUnsigned:
      f.buf.insert("(", start)
      f.write ">>>0)"
    of jsFloat, jsFloatish:
      f.buf.insert("fround(", start)
      f.write ")"
    of jsDouble:
      f.buf.insert("+", start)
    else:
      unreachable()

proc jump(f; target: int) =
  f.write "break L" & $target & ";"

proc toJs(t: TypeInfo): range[jsSigned..jsDouble] =
  t.kind

proc toJs(tree; types: NodeIndex, t: TypeId): JsType =
  toJs parseType(tree, types, t)

proc generic(x: JsType): JsType {.inline.} =
  if x in {jsSigned, jsUnsigned}:
    jsInt
  else:
    x

proc returnType(tree; types: NodeIndex, t: TypeId): JsType =
  let n = tree.child(types, int(t))
  case tree[n, 0].kind
  of Void: jsVoid
  of Type: generic toJs(tree, types, tree[n, 0].typ)
  else:    unreachable()

proc genCall(c; f; tree; call: NodeIndex,
             start: int, fin: BackwardsIndex): JsType =
  ## Generates the code a call. `start` and `fin` are where the relevant parts
  ## of the list in `call` start and end, respectively.
  if tree[call, start].kind == Proc:
    # it's a static call
    let id = tree[call, start].id
    let typ = tree.child(c.types, tree[tree.child(tree.child(2), id), 0].val.int)

    f.write "f" & $id & "("
    var i = 1
    for it in tree.items(call, start + 1, fin):
      if i > 1:
        f.write ", "
      c.genExpr(f, tree, it, generic toJs(tree, c.types, tree[typ, i].typ))
      inc i
    f.write ")"
    result = returnType(tree, c.types, tree[tree.child(tree.child(2), id), 0].typ)
  else:
    # it's an indirect call
    let bucket = c.tables.bucketMap[tree[call, start].typ]
    f.write "indirect" & $bucket & "[("
    c.genExpr(f, tree, tree.child(call, start + 1), jsIntish)
    f.write " - " & $(c.tables.buckets[bucket].start + 1) & ") & "
    f.write $(c.tables.buckets[bucket].elems.len-1) & "]("

    let typ = tree.child(c.types, tree[call, start].val.int)

    var i = 1
    for it in tree.items(call, start + 2, fin):
      if i > 1:
        f.write ", "
      c.genExpr(f, tree, it, generic toJs(tree, c.types, tree[typ, i].typ))
      inc i
    f.write ")"
    result = returnType(tree, c.types, tree[call, start].typ)

proc signExtend(c; f; typ: TypeInfo, inTyp: JsType): JsType =
  if typ.size < 4:
    let shift = 32 - (typ.size * 8)
    f.write " << " & $shift & " >> " & $shift
    jsSigned
  else:
    inTyp

proc mask(c; f; typ: TypeInfo, inTyp: JsType): JsType =
  if typ.size < 4:
    f.write " & " & $((1 shl (typ.size * 8)) - 1)
    jsSigned
  else:
    inTyp

proc genBinaryOp(c; f; tree; a, b: NodeIndex, binop: string, typ: JsType) =
  f.write "("
  c.genExpr(f, tree, a, typ)
  f.write " " & binop & " "
  c.genExpr(f, tree, b, typ)
  f.write ")"

proc genBinaryOp(c; f; tree; op: NodeIndex,
                 binop: string, s, u, fl, d: JsType): TypeInfo {.discardable.} =
  ## Generates the code for a two-operand operation, with the opcode picked
  ## based on the type.
  let (typ, a, b) = triplet(tree, op)
  result = parseType(tree, c.types, tree[typ].typ)
  genBinaryOp(c, f, tree, a, b, binop, s)

proc genBinaryArithOp(c; f; tree; op: NodeIndex, binop: string, s,u,fl,d: JsType): JsType =
  ## Similar to ``genBinaryOp``, but also handles uint overflow.
  let typ = c.genBinaryOp(f, tree, op, binop, s,u,fl,d)
  if typ.kind == jsUnsigned:
    # unsigned integers need to "wrap around" on overflow
    c.mask(f, typ, jsIntish)
  else:
    jsIntish

proc heapAccess(c; f; tree; typ: TypeInfo, e: NodeIndex): JsType =
  f.write:
    case typ.kind
    of jsSigned:
      case typ.size
      of 1: "HEAP_I8["
      of 2: "HEAP_I16["
      of 4: "HEAP_I32["
      else: unreachable()
    of jsUnsigned:
      case typ.size
      of 1: "HEAP_U8["
      of 2: "HEAP_U16["
      of 4: "HEAP_U32["
      else: unreachable()
    of jsFloat:
      "HEAP_F32["
    of jsDouble:
      "HEAP_F64["

  c.genExpr(f, tree, e, jsIntish)
  case typ.size
  of 1: f.write "]"
  of 2: f.write " >> 1]"
  of 4: f.write " >> 2]"
  of 8: f.write " >> 3]"
  else: unreachable()

  # per the asm.js specification:
  case typ.kind
  of jsSigned, jsUnsigned: jsIntish
  of jsFloat: jsFloat # TODO: wrong, it's 'float?'
  of jsDouble: jsDouble # TODO: wrong, it's 'dobule?'

proc typeof(c; tree; local: int): JsType =
  generic toJs(tree, c.types, tree[c.locals, local].typ)

proc genExpr(c; f; tree; val: NodeIndex): JsType =
  ## Generates the code for an expression (`val`), which is ``value`` in the
  ## grammar.
  ##
  ## The returned JS type is a subtype of the JS operation as documented in the
  ## asm.js spec.
  case tree[val].kind
  of IntVal:
    let val = tree.getInt(val)
    f.write $val
    if val >= 0 and val < high(int32):
      jsFixnum
    else:
      jsSigned
  of FloatVal:
    f.write $tree.getFloat(val)
    jsDouble
  of ProcVal:
    # always append 1 so that the zero value can represent "no procedure"
    # TODO: ^^ this should be handled by a higher-level language instead
    let (bucket, rel) = c.tables.procMap[tree[val].id]
    f.write $(c.tables.buckets[bucket].start + rel + 1)
    jsFixnum
  of Copy:
    case tree[val, 0].kind
    of Local:
      f.write "lo" & $tree[val, 0].id
      c.typeof(tree, tree[val, 0].id)
    of Global:
      f.write "g" & $tree[val, 0].id
      jsUnknown # TODO: we *do* know the type
    else:
      unreachable()
  of Load:
    let typ = parseType(tree, c.types, tree[val, 0].typ)
    c.heapAccess(f, tree, typ, tree.child(val, 1))
  of Addr:
    f.write "(bp + " & $tree.getInt(tree.child(val, 0)) & ")"
    jsIntish
  of Neg:
    let (typ, operand) = pair(tree, val)
    let t = toJs(tree, c.types, tree[typ].typ)
    f.write "-"
    c.genExpr(f, tree, operand, t)
    case t
    of jsDouble: jsDouble
    of jsFloat:  jsFloatish
    else:        jsIntish
  of Add:
    let (typ, a, b) = triplet(tree, val)
    let t = parseType(tree, c.types, tree[typ].typ)
    case toJs(t)
    of jsSigned: c.genBinaryOp(f, tree, a, b, "+", jsInt); jsIntish
    of jsUnsigned: c.genBinaryOp(f, tree, a, b, "+",  jsInt); c.mask(f, t, jsIntish)
    of jsFloat: c.genBinaryOp(f, tree, a, b, "+",  jsFloat); jsFloatish
    of jsDouble: c.genBinaryOp(f, tree, a, b, "+",  jsDouble); jsDouble
  of Sub:
    let (typ, a, b) = triplet(tree, val)
    let t = parseType(tree, c.types, tree[typ].typ)
    case toJs(t)
    of jsSigned: c.genBinaryOp(f, tree, a, b, "-", jsInt); jsIntish
    of jsUnsigned: c.genBinaryOp(f, tree, a, b, "-", jsInt); c.mask(f, t, jsIntish)
    of jsFloat: c.genBinaryOp(f, tree, a, b, "-", jsFloat); jsFloatish
    of jsDouble: c.genBinaryOp(f, tree, a, b, "-", jsDouble); jsDouble
  of Mul:
    let (typ, a, b) = triplet(tree, val)
    let t = parseType(tree, c.types, tree[typ].typ)
    case t.kind
    of jsSigned, jsUnsigned:
      f.write "imul("
      c.genExpr(f, tree, a, jsInt)
      f.write ", "
      c.genExpr(f, tree, b, jsInt)
      f.write ")"
      if t.kind == jsUnsigned:
        c.mask(f, t, jsSigned)
      else:
        jsSigned
    of jsFloat:
      c.genBinaryOp(f, tree, a, b, "*", jsFloat) # TODO: needs to be 'float?'
      jsFloatish
    of jsDouble:
      c.genBinaryOp(f, tree, a, b, "*", jsDouble) # TODO: needs to be 'double?'
      jsDouble
  of Div:
    let (typ, a, b) = triplet(tree, val)
    let t = parseType(tree, c.types, tree[typ].typ)
    case toJs(t)
    of jsSigned: c.genBinaryOp(f, tree, a, b, "/", jsSigned); jsIntish
    of jsUnsigned: c.genBinaryOp(f, tree, a, b, "/", jsUnsigned); jsIntish
    of jsFloat: c.genBinaryOp(f, tree, a, b, "/", jsFloat); jsFloatish
    of jsDouble: c.genBinaryOp(f, tree, a, b, "/", jsDouble); jsDouble
  of Mod:
    toJs c.genBinaryOp(f, tree, val, "%", jsIntish, jsIntish, jsDouble, jsDouble)
  of BitNot:
    let (typ, a) = pair(tree, val)
    let t = parseType(tree, c.types, tree[typ].typ)
    f.write "~"
    c.genExpr(f, tree, a, jsIntish)
    if t.kind == jsUnsigned:
      # discard the unused higher bits:
      c.mask(f, t, jsSigned)
    else:
      c.signExtend(f, t, jsSigned)
  of BitAnd:
    let (a, b) = pair(tree, val)
    c.genBinaryOp(f, tree, a, b, "&", jsIntish)
    jsSigned
  of BitOr:
    let (a, b) = pair(tree, val)
    c.genBinaryOp(f, tree, a, b, "|", jsIntish)
    jsSigned
  of BitXor:
    c.genBinaryArithOp(f, tree, val, "^", jsIntish, jsIntish, jsUnknown, jsUnknown)
  of Shl:
    let (typ, a, b) = triplet(tree, val)
    c.genExpr(f, tree, a, jsIntish)
    f.write " << "
    c.genExpr(f, tree, b, jsIntish)
    let t = parseType(tree, c.types, tree[typ].typ)
    if t.kind == jsSigned:
      c.signExtend(f, t, jsSigned)
    else:
      c.mask(f, t, jsSigned)
  of Shr:
    let (typ, a, b) = triplet(tree, val)
    c.genExpr(f, tree, a, jsIntish)
    case parseType(tree, c.types, tree[typ].typ).kind
    of jsSigned:   f.write " >> "  # arithmetic right-shift
    of jsUnsigned: f.write " >>> " # logical right-shift
    else:       unreachable()
    c.genExpr(f, tree, b, jsIntish)
    jsIntish
  of Not:
    f.write "!"
    c.genExpr(f, tree, tree.child(val, 0), jsInt)
    jsInt
  of Eq:
    c.genBinaryOp(f, tree, val, "==", jsSigned, jsUnsigned, jsFloat, jsDouble)
    jsInt
  of Lt:
    c.genBinaryOp(f, tree, val, "<", jsSigned, jsUnsigned, jsFloat, jsDouble)
    jsInt
  of Le:
    c.genBinaryOp(f, tree, val, "<=", jsSigned, jsUnsigned, jsFloat, jsDouble)
    jsInt
  of Reinterp:
    # reinterpret the bit pattern as another type
    let
      dtyp = parseType(tree, c.types, tree[val, 0].typ)
      styp = parseType(tree, c.types, tree[val, 1].typ)
    # sanity checks:
    assert dtyp.kind != styp.kind
    assert dtyp.size == styp.size

    case dtyp.kind
    of jsSigned, jsUnsigned:
      case styp.kind
      of jsSigned, jsUnsigned:
        c.genExpr(f, tree, tree.child(val, 2), jsInt)
        jsInt
      of jsFloat:
        # TODO: make sure the stack-pointer always stays 8-byte aligned
        f.write "(HEAP_F32[((sp + 7) & ~7) >> 2] = "
        c.genExpr(f, tree, tree.child(val, 2), jsFloatish)
        f.write ", HEAP_I32[((sp + 7) & ~7) >> 2])"
        jsIntish
      of jsDouble:
        unreachable()
    of jsFloat, jsDouble:
      unreachable()
  of Conv:
    # numeric conversion
    let
      dtyp = parseType(tree, c.types, tree[val, 0].typ)
      styp = parseType(tree, c.types, tree[val, 1].typ)

    case dtyp.kind
    of jsSigned:
      case styp.kind
      of jsSigned, jsUnsigned:
        c.genExpr(f, tree, tree.child(val, 2), jsInt)
        c.signExtend(f, dtyp, jsInt)
        # leave coercing to the caller
      of jsDouble, jsFloat:
        f.write "(~~"
        c.genExpr(f, tree, tree.child(val, 2), styp.kind)
        f.write ")"
        jsSigned
    of jsUnsigned:
      case styp.kind
      of jsSigned, jsUnsigned:
        c.genExpr(f, tree, tree.child(val, 2), jsInt)
        # the upper bits can only be set if the source type has larger bit-
        # width than the destination
        if dtyp.size < styp.size:
          c.mask(f, dtyp, jsInt)
        else:
          jsInt # leave coercing to unsigned to the caller
      of jsDouble, jsFloat:
        f.write "(~~"
        c.genExpr(f, tree, tree.child(val, 2), styp.kind)
        f.write ")"
        jsSigned # leave coercing to unsigned to the caller
    of jsFloat:
      c.genExpr(f, tree, tree.child(val, 2), jsFloat)
      jsFloat
    of jsDouble:
      c.genExpr(f, tree, tree.child(val, 2), jsDouble)
      jsDouble

  of Call:
    c.genCall(f, tree, val, 0, ^1)
  else:
    unreachable()

proc genChoice(c; f; tree; choice: NodeIndex) =
  ## Generates the code for ``Choice`` tree, where `val` is the selector and
  ## `typ` the selector's type.
  f.write "case "
  c.genExpr(f, tree, tree.child(choice, 0), jsSigned)
  f.write ": "
  f.jump(tree[tree.child(choice, 1), 0].imm)
  f.writeLine ""

proc genExit(f; c; tree; exit: NodeIndex) =
  ## Generates the code for a continuation exit.
  case tree[exit].kind
  of Continue:
    case tree.len(exit)
    of 1:
      let i = tree[exit, 0].imm
      if i.int != c.current + 1:
        f.writeLine "break L" & $i & ";"
    of 2:
      # continue with argument can only mean return
      # TODO: this is wrong. The stack pointer must be reset *after* the
      #       return value is computed, since the expression might depend on
      #       the stack-pointer (directly or indirectly)
      if c.usesSp:
        f.writeLine "sp = bp;"
      f.write "return "
      c.genExpr(f, tree, tree.child(exit, 1), c.returnType, force=true)
      f.writeLine ";"
    else:
      unreachable()
  of Loop:
    dec f.indent
    f.writeLine "}"
  of SelectBool:
    let (sel, a, b) = triplet(tree, exit)
    f.write "if ("
    c.genExpr(f, tree, sel, jsInt)
    f.write ") { "
    f.jump(tree[a, 0].imm)
    f.write " } else { "
    f.jump(tree[b, 0].imm)
    f.writeLine " }"
  of Select:
    let
      val = tree.child(exit, 1) # the value to select the target with
    f.write "switch ("
    # unsigned integers are coerced into signed ones
    c.genExpr(f, tree, val, jsSigned)
    f.writeLine ") {"
    for it in tree.items(exit, 2, ^2):
      c.genChoice(f, tree, it)
    f.write "default: "
    f.jump(tree[tree.last(tree.last(exit)), 0].imm)
    f.writeLine ""
    f.writeLine "}"
  of Unreachable:
    discard "a no-op"
  else:
    unreachable()

proc genStmt(f; c; tree; n: NodeIndex) =
  ## Generates the bytecode for a statement (`n`).
  case tree[n].kind
  of Asgn:
    f.write "lo" & $tree[n, 0].id & " = "
    c.genExpr(f, tree, tree.child(n, 1), c.typeof(tree, tree[n, 0].id))
    f.writeLine ";"
  of Store:
    let
      (tn, a, b) = triplet(tree, n)
      typ = parseType(tree, c.types, tree[tn].typ)

    let jt = c.heapAccess(f, tree, typ, a)
    f.write " = "
    c.genExpr(f, tree, b, jt) # TODO: using `jt` is not really correct here
    f.writeLine ";"
  of Copy:
    let (a, b, size) = triplet(tree, n)
    f.write "memcopy("
    c.genExpr(f, tree, a, jsInt)
    f.write ", "
    c.genExpr(f, tree, b, jsInt)
    f.write ", "
    c.genExpr(f, tree, size, jsInt)
    f.writeLine ");"
  of Clear:
    let (a, size) = pair(tree, n)
    f.write "memclear("
    c.genExpr(f, tree, a, jsInt)
    f.write ", "
    c.genExpr(f, tree, size, jsInt)
    f.writeLine ");"
  of Call:
    discard c.genCall(f, tree, n, 0, ^1)
    f.writeLine ";"
  of Drop:
    discard c.genExpr(f, tree, tree.child(n, 0))
    f.writeLine ";"
  else:
    unreachable()

proc gen(f: var Formatter, c; tree; n: NodeIndex) =
  ## Generates bytecode for the given continuation.
  if c.nodes[c.current].isTarget:
    dec f.indent
    f.writeLine "}"

  for it in c.nodes[c.current].labels.items:
    if it.isLoop:
      f.writeLine "while (1) {"
      inc f.indent
    else:
      f.writeLine "L" & $it.val & ": {"
      inc f.indent

  if c.usesSp:
    f.writeLine "sp = (bp + " & $tree[n, 1].imm & ")|0;"

  for it in tree.items(n, 2, ^2):
    genStmt(f, c, tree, it)

  genExit(f, c, tree, tree.last(n))

proc default(f: var Formatter, typ: JsType) =
  case typ
  of jsSigned, jsUnsigned:
    f.write "0"
  of jsFloat:
    f.write "fround(0.0)"
  of jsDouble:
    f.write "0.0"
  else:
    unreachable()

proc scan(tree; conts: NodeIndex): seq[GraphNode] =
  result.newSeq(tree.len(conts))

  proc scanAux(tree; cont: NodeIndex, i: int32): GraphNode =
    proc addNoDup[T](s: var seq[T], val: T) =
      if val notin s:
        s.add val

    let exit = tree.last(cont)
    case tree[exit].kind
    of SelectBool:
      result.exits.addNoDup tree[tree.child(exit, 1), 0].imm
      result.exits.addNoDup tree[tree.child(exit, 2), 0].imm
    of Select:
      for it in tree.items(exit, 2):
        result.exits.addNoDup tree[tree.last(it), 0].imm
    of Loop:
      result.isLoop = true
      result.exits = @[tree[exit, 0].imm]
    of Continue:
      if tree.len(exit) == 1:
        let e = tree[exit, 0].imm
        if e != i + 1:
          result.exits = @[tree[exit, 0].imm]
    else:
      echo tree[exit].kind
      unreachable()

    result.firstExit = high(int)

  for i, it in tree.pairs(conts):
    if tree.len(it) > 1:
      result[i] = scanAux(tree, it, i.int32)
    else:
      result[i].firstExit = high(int)

  for i, it in result.mpairs:
    if it.isLoop:
      result[it.exits[0]].labels.add (true, i)
    else:
      for e in it.exits.items:
        result[e].isTarget = true
        result[e].firstExit = min(result[e].firstExit, i)

  for i, it in result.mpairs:
    if it.firstExit != high(int):
      var x = 0
      while x < result[it.firstExit].labels.len:
        if result[it.firstExit].labels[x].val < i:
          break
        inc x
      result[it.firstExit].labels.insert((false, i), x)

proc translate(f: var Formatter, tables: Tables, tree; types, def: NodeIndex) =
  ## Translates the single procedure body `body` to VM bytecode. `types`
  ## provides the type environment.
  let (typ, locals, conts) = tree.triplet(def)

  var c = PassCtx(types: types, locals: locals, tables: addr tables)

  let procTy = tree.child(types, tree[typ].val.int)
  let numParams = tree.len(procTy) - 1

  if tree[procTy, 0].kind != Void:
    c.returnType = generic toJs(tree, types, tree[procTy, 0].typ)

  f.write "("
  # put all parameters into locals:
  for i in countdown(numParams, 1):
    if i < numParams:
      f.write ", "
    f.write "lo" & $(numParams - i)
  f.writeLine ") {"
  inc f.indent

  for i in 0..<numParams:
    f.write "lo" & $i & " = "
    f.conv(generic toJs(tree, types, tree[locals, i].typ), "lo" & $i)
    f.writeLine ";"

  # compute the maximum amount of required stack space:
  for it in tree.items(conts):
    if tree.len(it) > 1: # ignore the return continuation
      if tree[it, 1].imm > 0:
        c.usesSp = true
        break

  if c.usesSp or tree.len(locals) > numParams:
    f.write "var "

  var first = true

  # setup the stack pointer, if one is required:
  if c.usesSp:
    f.write "bp = 0"
    first = false

  for i in numParams..<tree.len(locals):
    let it = tree.child(locals, i)
    if not first:
      f.write ", "
    first = false
    f.write "lo" & $i & " = "
    f.default(toJs(tree, c.types, tree[it].typ))

  if not first:
    f.writeLine ";"

  if c.usesSp:
    f.writeLine "bp = sp;"

  c.nodes = scan(tree, conts)

  for i, cont in tree.pairs(conts):
    c.current = i
    if tree.len(cont) == 1:
      if tree.len(tree.child(cont, 0)) == 0:
        if c.usesSp:
          f.writeLine "sp = bp;"
        f.writeLine "return;"
    else:
      gen(f, c, tree, cont)

proc translate*(module: PackedTree[NodeKind]): string =
  ## Translates a complete module to the VM bytecode and the associated
  ## environmental data.
  let (types, globals, procs) = module.triplet(NodeIndex(0))

  var code: Formatter
  code.writeLine("function module(stdlib, foreign, heap) {")
  inc code.indent
  code.writeLine("\"use asm\";")

  # TODO: only emit the globals that are actually used
  code.writeLine "var sp = 0;"
  code.writeLine "var fround = stdlib.Math.fround;"
  code.writeLine "var imul = stdlib.Math.imul;"
  code.writeLine "var HEAP_I8 = new stdlib.Int8Array(heap);"
  code.writeLine "var HEAP_I16 = new stdlib.Int16Array(heap);"
  code.writeLine "var HEAP_I32 = new stdlib.Int32Array(heap);"
  code.writeLine "var HEAP_U8 = new stdlib.Uint8Array(heap);"
  code.writeLine "var HEAP_U16 = new stdlib.Uint16Array(heap);"
  code.writeLine "var HEAP_U32 = new stdlib.Uint32Array(heap);"
  code.writeLine "var HEAP_F32 = new stdlib.Float32Array(heap);"
  code.writeLine "var HEAP_F64 = new stdlib.Float64Array(heap);"

  # add the defined globals to the environment:
  for i, def in module.pairs(globals):
    # the type is inferred from the value's node kind
    code.write "var g" & $i & " = "
    # TODO: the float/double distinction is missing
    case module[def].kind
    of FloatVal:
      code.write $getFloat(module, def)
    of IntVal:
      # always treat as signed
      code.write $getInt(module, def)
    else:
      unreachable()

    code.writeLine ";"

  var tables: Tables
  # TODO: only procedures that are used as values need to be placed in the
  #       buckets
  # compute the procedure buckets:
  for i, def in module.pairs(procs):
    let typ = module[def, 0].typ
    let b = tables.bucketMap.mgetOrPut(typ, tables.buckets.len)
    if b == tables.buckets.len:
      # a new bucket is needed
      tables.buckets.add default(ProcBucket)

    tables.buckets[b].elems.add i.int32
    tables.procMap.add (i, tables.buckets[b].elems.high)

  # compute the procedure bucket starts:
  block:
    var start = 0
    for it in tables.buckets.mitems:
      it.start = start
      start += it.elems.len

  # generate the code for the procedures and add them to the environment:
  for i, def in module.pairs(procs):
    code.write "function f" & $i
    translate(code, tables, module, types, def)
    dec code.indent
    code.writeLine "}"

  # TODO: only emit memcopy and memclear when actually used
  # TODO: use properly optimized memcopy and memclear procedures. Alignment
  #       and size are oftentimes known at the callsite, so no run-time
  #       dispatch / alignment is necessary in that case
  code.writeLine "function memcopy(dst, src, num) {"
  inc code.indent
  code.writeLine "dst = dst|0; src = src|0; num = num|0;"
  code.writeLine "var i = 0"
  code.writeLine "for (; (i|0) < (num|0); i = (i + 1)|0) HEAP_U8[dst + i] = HEAP_U8[src + i];"
  dec code.indent
  code.writeLine "}"

  code.writeLine "function memclear(dst, num) {"
  inc code.indent
  code.writeLine "dst = dst|0; num = num|0;"
  code.writeLine "var i = 0"
  code.writeLine "for (; (i|0) < (num|0); i = (i + 1)|0) HEAP_U8[dst + i] = 0;"
  dec code.indent
  code.writeLine "}"

  # TODO: pad the tables to have a power-of-two length
  for b, it in tables.buckets.pairs:
    code.write "var indirect" & $b & " = ["
    for i, def in it.elems.pairs:
      if i > 0:
        code.write ", "
      code.write "f" & $def
    code.writeLine "]"

  code.writeLine "return f" & $(module.len(procs) - 1) & ";"
  dec code.indent
  code.writeLine "}"

  code.writeLine "var stdlib = {Math: { fround: Math.fround, imul: Math.imul }, Int8Array: Int8Array, Int16Array: Int16Array, Int32Array: Int32Array, Uint8Array: Uint8Array, Uint16Array: Uint16Array, Uint32Array: Uint32Array, Float32Array: Float32Array, Float64Array: Float64Array };"
  code.writeLine "var heap = new ArrayBuffer(0x10000);"
  code.writeLine "var mod = module(stdlib, null, heap);"
  code.writeLine "console.log(mod());"

  result = code.buf
