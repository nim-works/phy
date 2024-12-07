## This implements a temporary pass for translating the parse-tree of the
## source language into the currently highest-level intermediate language.
## It's there so that development of the source language can already commence
## while the the intermediate languages are still being developed.
##
## The focus is on correctness. Performance, code quality, and overall
## architecture (of this module) are of secondary concern.

import
  std/[algorithm, sequtils, tables],
  passes/[builders, spec, trees],
  phy/[reporting, types],
  vm/[utils]

from std/strutils import `%`

import passes/spec_source except NodeKind

type
  SourceKind = spec_source.NodeKind
  InTree     = PackedTree[SourceKind]
  Node       = TreeNode[NodeKind]
  NodeSeq    = seq[Node]

  EntityKind = enum
    ekNone        ## signals "non-existent"
    ekBuiltinVal  ## some built-in named value
    ekBuiltinProc ## some built-in procedure
    ekProc
    ekType
    ekLocal
    ekParam

  Entity = object
    kind: EntityKind
    id: int
      ## ID of the procedure or type. It's an index into the respective list

  ProcInfo* = object
    typ*: SemType
      ## the procedure's type

  Scope = Table[string, Entity]

  ModuleCtx* = object
    ## The translation/analysis context for a single module.
    reporter: ref ReportContext[string]
    # XXX: strings being used for diagnostics is a temporary measure. Message
    #      formatting should eventually be separated from diagnostic emission

    literals: Literals
    types: Builder[NodeKind]
      ## the in-progress type section
    numTypes: int
    aliases: seq[SemType]
      ## the list of type aliases
    procs: Builder[NodeKind]
      ## the in-progress procedure section
    procList*: seq[ProcInfo]

    procTypeCache: Table[SemType, uint32]
      ## caches the ID of IL signature types generated for procedure types.
      ## They're structural types in the source language, but nominal types in
      ## the target IL

    scopes: seq[Scope]
      ## the stack of scopes. The last item always represents the current scope

    # procedure context:
    retType: SemType
    returnParam: uint32
      ## the index of the out parameter, if one is required
    locals: seq[SemType]
      ## all locals part of the procedure
    params: seq[tuple[typ: SemType, local: uint32]]
      ## the parameters for the procedure

  ExprFlag {.pure.} = enum
    Lvalue ## the expression is an lvalue. The flags absence implies
           ## that the expression is an rvalue or void expression
    Mutable## the expression refers to a mutable lvalue. Only makes sense
           ## when the ``Lvalue`` flag is present

  ExprType = tuple
    ## Returned by expression analysis. Carries additional attributes about
    ## the expression, not just the type.
    typ: SemType
    attribs: set[ExprFlag]

  Expr = object
    # XXX: the target IL doesn't support expression lists (yet), so we have
    #      to apply the necessary lowering here, for now. Efficiency doesn't
    #      matter
    stmts: seq[NodeSeq] # can be empty
    expr: NodeSeq
    typ: SemType
    attribs: set[ExprFlag]

const
  BuiltIns = {
    "+": ekBuiltinProc,
    "-": ekBuiltinProc,
    "==": ekBuiltinProc,
    "<=": ekBuiltinProc,
    "<": ekBuiltinProc,
    "not": ekBuiltinProc,
    "true": ekBuiltinVal,
    "false": ekBuiltinVal
  }.toTable

  UnitNode = Node(kind: IntVal)
    ## the node representing the unitary value
  unitExpr = Expr(expr: @[UnitNode], typ: prim(tkUnit))
    ## the expression evaluating to the unitary value

  pointerType = prim(tkInt)
    ## the type inhabited by pointer values. The constant is used as a
    ## placeholder until a dedicated pointer type is introduced

using
  c: var ModuleCtx
  t: InTree
  bu: var Builder[NodeKind]
  stmts: var seq[NodeSeq]

template `+`(t: SemType, a: set[ExprFlag]): ExprType =
  ## Convenience shortcut for creating an ``ExprType``.
  (typ: t, attribs: a)

proc error(c; message: sink string) =
  ## Sends the error diagnostic `message` to the reporter.
  c.reporter.error(message)

func lookup(c: ModuleCtx, name: string): Entity =
  ## Implements the lookup action described in the specification.
  var i = c.scopes.high
  while i >= 0:
    result = c.scopes[i].getOrDefault(name, Entity(kind: ekNone))
    if result.kind != ekNone:
      return
    dec i

  # try the builtins
  result.kind = BuiltIns.getOrDefault(name, ekNone)

func addDecl(c; name: string, entity: sink Entity) =
  ## Adds the `entity` with name `name` to the current scope, ignoring whether
  ## it already existed.
  c.scopes[^1][name] = entity

func removeDecl(c; name: string) =
  ## Removes the entity with `name` from the current scope.
  c.scopes[^1].del(name)

func openScope(c) =
  ## Opens a new scope and makes it the current one.
  c.scopes.add default(typeof(c.scopes[0]))

func closeScope(c) =
  ## Closes the current scope and makes its parent the current one.
  c.scopes.shrink(c.scopes.len - 1)

func add(bu; trees: openArray[NodeSeq]) =
  ## Appends all `trees` to the current sub-tree. The trees must each either
  ## represent a single atomic node, or a complete subtree.
  for t in trees.items:
    bu.add t

template addType(c; kind: NodeKind, body: untyped): uint32 =
  c.types.subTree kind:
    body
  (let r = c.numTypes; inc c.numTypes; r.uint32)

proc addType(c; node: Node): uint32 =
  c.types.add node
  result = c.numTypes.uint32
  inc c.numTypes

proc expect(c; name: string, ent: Entity, kind: EntityKind): bool =
  ## Convenience procedure for reporting an error if `ent` is not of the given
  ## `kind`. Returns 'true' if it is.
  if ent.kind == kind:
    true
  elif ent.kind == ekNone:
    c.error("undeclared identifier: '" & name & "'")
    false
  else:
    c.error("'" & name & "' is not a " & $kind & " name")
    false

proc expectNot(c; typ: sink SemType, kind: TypeKind): SemType =
  ## If `typ` has the given `kind`, reports an error and returns the error
  ## type. Otherwise returns `typ` as-is.
  if typ.kind != kind:
    result = typ
  else:
    c.error("type not allowed in this context")
    result = errorType()

proc evalType(c; t; n: NodeIndex): SemType =
  ## Evaluates a type expression, yielding the resulting type.
  case t[n].kind
  of VoidTy:  prim(tkVoid)
  of UnitTy:  prim(tkUnit)
  of BoolTy:  prim(tkBool)
  of IntTy:   prim(tkInt)
  of FloatTy: prim(tkFloat)
  of TupleTy:
    if t.len(n) == 0:
      prim(tkUnit)
    else:
      var tup = SemType(kind: tkTuple)
      for it in t.items(n):
        tup.elems.add evalType(c, t, it)
        case tup.elems[^1].kind
        of tkError:
          tup = errorType()
          break
        of tkVoid:
          c.error("'void' type cannot be part of tuple type")
          tup = errorType()
          break
        else:
          discard "all good"

      tup
  of UnionTy:
    var list = newSeq[SemType]()
    for i, it in t.pairs(n):
      # make sure to add the types in a sorted fashion, so that
      # ``union(int, float)`` and ``union(float, int)`` result in the same type
      let
        typ = c.expectNot(c.evalType(t, it), tkVoid)
        at = lowerBound(list, typ, cmp)

      if at < list.len and list[at] == typ:
        if typ.kind != tkError:
          c.error("union type operands must be unique")
      else:
        list.add typ

    SemType(kind: tkUnion, elems: list)
  of SourceKind.ProcTy:
    # anything goes as the return type
    var list = @[c.evalType(t, t.child(n, 0))]

    for it in t.items(n, 1):
      list.add c.expectNot(c.evalType(t, it), tkVoid)

    SemType(kind: tkProc, elems: list)
  of Ident:
    let
      name = t.getString(n)
      ent  = c.lookup(name)
    if c.expect(name, ent, ekType):
      c.aliases[ent.id]
    else:
      errorType()
  else:       unreachable() # syntax error

proc typeToIL(c; typ: SemType): uint32 =
  case typ.kind
  of tkVoid:
    unreachable()
  of tkUnit:
    # XXX: there's no unit type in the target IL, and in order to not having
    #      to rewrite all ``unit`` type usages here, we're translating the
    #      type to a 1-byte integer
    c.addType Node(kind: Int, val: 1)
  of tkBool:
    c.addType Node(kind: Int, val: 1)
  of tkInt, tkError:
    c.addType Node(kind: Int, val: 8)
  of tkFloat:
    c.addType Node(kind: Float, val: 8)
  of tkTuple:
    let args = mapIt(typ.elems, c.typeToIL(it))
    c.addType Record:
      c.types.add Node(kind: Immediate, val: size(typ).uint32)
      var off = 0 ## the current field offset
      for i, it in args.pairs:
        c.types.subTree Field:
          c.types.add Node(kind: Immediate, val: off.uint32)
          c.types.add Node(kind: Type, val: it)
        off += size(typ.elems[i])
  of tkUnion:
    let args = mapIt(typ.elems, c.typeToIL(it))
    let inner = c.addType Record:
      c.types.add Node(kind: Immediate, val: size(typ).uint32 - 8)
      for it in args.items:
        c.types.subTree Field:
          c.types.add Node(kind: Immediate, val: 0)
          c.types.add Node(kind: Type, val: it)

    let tag = c.typeToIL(prim(tkInt))
    c.addType Record:
      c.types.add Node(kind: Immediate, val: size(typ).uint32)
      # the tag field:
      c.types.subTree Field:
        c.types.add Node(kind: Immediate, val: 0)
        c.types.add Node(kind: Type, val: tag)
      # the actual union:
      c.types.subTree Field:
        c.types.add Node(kind: Immediate, val: 8)
        c.types.add Node(kind: Type, val: inner)
  of tkProc:
    # a proc type is used to represent both procedure signatures and the type
    # of procedural values. For values, the underlying storage type is a uint
    c.addType Node(kind: UInt, val: 8)

proc rawGenProcType(c; typ: SemType): uint32 =
  ## Generates the IL representation for the procedure signature type `typ`
  ## and adds it to `c`.
  assert typ.kind == tkProc
  let params = mapIt(typ.elems.toOpenArray(1, typ.elems.high)):
    if it.kind in AggregateTypes:
      # XXX: due to lack of support in the IL, aggregate values need to be
      #      passed by address at the moment
      c.typeToIL(pointerType)
    else:
      c.typeToIL(it)

  template addParams() =
    for p in params.items:
      c.types.add Node(kind: Type, val: p)

  case typ.elems[0].kind
  of tkVoid:
    c.addType ProcTy:
      c.types.subTree Void: discard
      addParams()
  of AggregateTypes:
    # aggregate types are passed via an out parameter.
    # ``() -> T`` becomes ``(int) -> unit``
    let
      ret = c.typeToIL(prim(tkUnit))
      arg = c.typeToIL(prim(tkInt))
    c.addType ProcTy:
      c.types.add Node(kind: Type, val: ret)
      addParams()
      c.types.add Node(kind: Type, val: arg)
  else:
    let typId = c.typeToIL(typ.elems[0])
    c.addType ProcTy:
      c.types.add Node(kind: Type, val: typId)
      addParams()

proc genProcType(c; typ: SemType): uint32 =
  ## Generates and caches the IL representation for the procedure signature
  ## type `typ`, or returns the cached ID if it already exists.
  c.procTypeCache.withValue typ, val:
    result = val[]
  do:
    result = rawGenProcType(c, typ)
    c.procTypeCache[typ] = result

template buildTree(kind: NodeKind, body: untyped): NodeSeq =
  ## Makes a builder available to `body`, evaluates `body`, and returns the
  ## generated tree.
  var res: NodeSeq
  if true: # open a new scope
    var bu {.inject.} = initBuilder[NodeKind](kind)
    body
    res = finish(bu)
  res

template addStmt(stmts: var seq[NodeSeq], body: untyped) =
  if true: # open a new scope
    var bu {.inject.} = initBuilder[NodeKind]()
    body
    stmts.add finish(bu)

template addStmt(stmts: var seq[NodeSeq], kind: NodeKind, body: untyped) =
  stmts.add buildTree(kind, body)

proc resetProcContext(c) =
  c.locals.setLen(0) # re-use the memory

proc newTemp(c; typ: SemType): uint32 =
  ## Allocates a new temporary of `typ` type.
  case typ.kind
  of tkVoid: discard "do not create a temp for void"
  else:
    result = c.locals.len.uint32
    c.locals.add typ

proc genLocal(val: uint32, typ: SemType, bu) =
  ## Emits a ``Local val`` to `bu`, so long as `typ` is not `tkVoid`.
  case typ.kind
  of tkVoid: discard "nothing to generate"
  else: bu.add Node(kind: Local, val: val)

proc genUse(a: Node|NodeSeq, bu) =
  ## Emits `a` to `bu`, wrapping the expression in a ``Copy`` operation when
  ## it's an lvalue expression.
  case (when a is Node: a.kind else: a[0].kind)
  of Field, At, Local:
    bu.subTree Copy:
      bu.add a
  of Deref:
    when a is NodeSeq:
      # ``(Deref typ x)`` -> ``(Load typ x)``
      bu.subTree Load:
        bu.add a[1]
        bu.add a.toOpenArray(2, a.high)
    else:
      unreachable()
  else:
    bu.add a

proc genUse(e: Expr, bu; stmts) =
  ## Emits a usage of expression `e` to `bu` and `stmts`.
  stmts.add e.stmts
  genUse(e.expr, bu)

proc genAsgn(c; a: Node|NodeSeq, b: NodeSeq, typ: SemType, bu) =
  ## Emits an ``a = b`` assignment to `bu`. For convenience, if `typ` is a
  ## ``tkVoid``, no assignment is emitted.
  if typ.kind != tkVoid:
    bu.subTree Asgn:
      bu.add a
      genUse(b, bu)

proc genDrop(a: Node|NodeSeq, typ: SemType, bu) =
  ## Emits a ``Drop a`` to `bu`, so long as `typ` is not `void`.
  if typ.kind != tkVoid:
    bu.subTree Drop:
      genUse(a, bu)

proc inline(bu; e: sink Expr; stmts) =
  ## Appends the trailing expression directly to `bu`.
  stmts.add e.stmts
  bu.add e.expr

proc capture(c; e: sink Expr; stmts): Node =
  ## Commits expression `e` to a fresh temporary. This is part of the
  ## expression-list lowering machinery.
  let tmp = c.newTemp(e.typ)
  result = Node(kind: Local, val: tmp)

  stmts.add e.stmts
  stmts.addStmt:
    c.genAsgn(result, e.expr, e.typ, bu)

proc fitExpr(c; e: sink Expr, target: SemType): Expr =
  ## Makes sure `e` fits into the `target` type, returning the expression
  ## with the appropriate conversion operation applied. If the type of `e`
  ## is not the same as or a subtype of `target`, an error is reported.
  if e.typ == target:
    result = e
  elif e.typ.isSubtypeOf(target):
    if e.typ.kind == tkVoid:
      result = e
    else:
      result = Expr(stmts: e.stmts, typ: target)
      case target.kind
      of tkUnion:
        # construct a union
        let
          tmp = c.newTemp(target)
          idx = find(target.elems, e.typ)

        # ignore the type not being found in the union. This indicates that an
        # error occurred during union construction

        # emit the tag assignment:
        result.stmts.addStmt Asgn:
          bu.subTree Field:
            bu.add Node(kind: Local, val: tmp)
            bu.add Node(kind: Immediate, val: 0)
          bu.add Node(kind: IntVal, val: c.literals.pack(idx))

        # emit the value assignment:
        result.stmts.addStmt Asgn:
          bu.subTree Field:
            bu.subTree Field:
              bu.add Node(kind: Local, val: tmp)
              bu.add Node(kind: Immediate, val: 1)
            bu.add Node(kind: Immediate, val: idx.uint32)
          genUse(e.expr, bu)

        result.expr = @[Node(kind: Local, val: tmp)]
      of tkError:
        # error correction: keep the original expression as is when fitting
        # to the error type
        result.typ = e.typ
        result.expr = e.expr
      else:
        unreachable()
  else:
    # TODO: this needs a better error message
    c.error("type mismatch")
    result = Expr(stmts: e.stmts, expr: @[Node(kind: IntVal)],
                  typ: errorType())

proc fitExprStrict(c; e: sink Expr, typ: SemType): Expr =
  ## Makes sure expression `e` fits `typ` exactly, reporting an error and
  ## returning an error-expression if not.
  if e.typ == typ:
    result = e # all good
  else:
    c.error("expected expression of type $1 but got type $2" %
            [$typ.kind, $e.typ.kind])
    # turn into an error expression:
    result = Expr(stmts: e.stmts, expr: @[Node(kind: IntVal)],
                  typ: errorType())

proc exprToIL(c; t: InTree, n: NodeIndex, bu, stmts): ExprType

proc exprToIL(c; t: InTree, n: NodeIndex): Expr =
  var bu = initBuilder[NodeKind]()
  (result.typ, result.attribs) = exprToIL(c, t, n, bu, result.stmts)
  result.expr = finish(bu)
  # verify some postconditions:
  assert result.typ.kind != tkVoid or result.expr.len == 0,
         "void `Expr` cannot have a trailing expression"
  assert result.typ.kind in {tkVoid, tkError} or result.expr.len > 0,
         "non-void `Expr` must have a trailing expression"

proc scopedExprToIL(c; t; n: NodeIndex): Expr =
  ## Analyzes the given expression and generates the IL for it. Analysis
  ## happens within a new scope, which is discarded afterwards.
  c.openScope()
  result = c.exprToIL(t, n)
  c.closeScope()

template lenCheck(t; n: NodeIndex, bu; expected: int) =
  ## Exits the current analysis procedure with an error, if `n` doesn't have
  ## `expected` children.
  if t.len(n) != expected:
    c.error("expected " & $expected & " arguments, but got " & $t.len(n))
    bu.add Node(kind: IntVal)
    return errorType()

proc binaryArithToIL(c; t; n: NodeIndex, name: string, bu, stmts): SemType =
  ## Analyzes and emits the IL for a binary arithmetic operation.
  lenCheck(t, n, bu, 3)

  let
    (_, a, b)  = t.triplet(n)
    eA = exprToIL(c, t, a)
    eB = exprToIL(c, t, b)

  let op =
    case name
    of "+": Add
    of "-": Sub
    else:   unreachable()

  if tkError in {eA.typ.kind, eB.typ.kind}:
    result = errorType()
  elif eA.typ != eB.typ:
    c.error("arguments have mismatching types")
    result = errorType()
  elif eA.typ.kind notin {tkInt, tkFloat}:
    c.error("arguments must be of 'int' or 'float' type")
    result = errorType()
  else:
    bu.subTree op:
      bu.add Node(kind: Type, val: c.typeToIL(eA.typ))
      bu.subTree Copy:
        bu.add c.capture(eA, stmts)
      bu.subTree Copy:
        bu.add c.capture(eB, stmts)

    result = eA.typ

proc relToIL(c; t; n: NodeIndex, name: string, bu; stmts): SemType =
  ## Analyzes and emits the IL for a relational operation.
  lenCheck(t, n, bu, 3)

  let
    (_, a, b)  = t.triplet(n)
    eA = exprToIL(c, t, a)
    eB = exprToIL(c, t, b)

  let (op, valid) =
    case name
    of "==": (Eq, {tkBool, tkInt, tkFloat})
    of "<":  (Lt, {tkInt, tkFloat})
    of "<=": (Le, {tkInt, tkFloat})
    else:   unreachable()

  if eA.typ == eB.typ and eA.typ.kind in valid:
    bu.subTree op:
      bu.add Node(kind: Type, val: c.typeToIL(eA.typ))
      bu.subTree Copy:
        bu.add c.capture(eA, stmts)
      bu.subTree Copy:
        bu.add c.capture(eB, stmts)

    result = prim(tkBool)
  elif tkError in {eA.typ.kind, eB.typ.kind}:
    result = errorType()
  else:
    c.error("arguments have mismatching types")
    bu.add Node(kind: IntVal)
    result = errorType()

proc notToIL(c; t; n: NodeIndex, bu; stmts): SemType =
  lenCheck(t, n, bu, 2)

  let arg = exprToIL(c, t, t.child(n, 1))

  if arg.typ.kind == tkBool:
    # a single argument, so no capture is necessary
    bu.subTree Not:
      genUse(arg, bu, stmts)
    result = prim(tkBool)
  else:
    c.error("expected 'bool' expression")
    bu.add Node(kind: IntVal)
    result = errorType()

proc userCallToIL(c; t; n: NodeIndex, bu; stmts): SemType =
  ## Analyzes a non-built-in call expression and translates it to its IL
  ## representation.
  let callee = c.exprToIL(t, t.child(n, 0))

  if callee.typ.kind == tkProc:
    proc useCallee(c; e: sink Expr, bu; stmts) =
      stmts.add e.stmts
      if e.expr[0].kind == ProcVal:
        # the callee is a statically-known procedure; it's a static call
        bu.add Node(kind: Proc, val: e.expr[0].val)
      else:
        bu.add Node(kind: Type, val: c.genProcType(e.typ))
        genUse(e.expr, bu)

    proc argsToIL(c; t; n: NodeIndex; prc: SemType, bu; stmts) {.nimcall.} =
      var i = 1 # 1 means argument 0
      for it in t.items(n, 1):
        # only try fitting the argument if there's a corresponding parameter
        let arg =
          if i < prc.elems.len:
            c.fitExprStrict(c.exprToIL(t, it), prc.elems[i])
          else:
            c.exprToIL(t, it)

        # capture the value to ensure a correct evaluation order between the
        # argument expressions
        let tmp = c.capture(arg, stmts)
        if arg.typ.kind in AggregateTypes:
          # XXX: due to lack of support in the IL, aggregate values need to be
          #      passed by address at the moment
          bu.subTree Addr:
            bu.add tmp
        else:
          genUse(tmp, bu)

        inc i

      if i != prc.elems.len:
        # arity mismatch
        c.error("expected $1 arguments but got $2" %
                [$(prc.elems.len - 1), $(i - 1)])

    # some return types need special handling
    case callee.typ.elems[0].kind
    of tkVoid:
      stmts.addStmt Call:
        c.useCallee(callee, bu, stmts)
        c.argsToIL(t, n, callee.typ, bu, stmts)
      # mark the non-exceptional call exit as unreachable:
      stmts.addStmt Unreachable:
        discard
    of AggregateTypes:
      # the value is not returned normally, but passed via an out parameter
      let tmp = c.newTemp(callee.typ.elems[0])
      stmts.addStmt Drop:
        bu.subTree Call:
          c.useCallee(callee, bu, stmts)
          c.argsToIL(t, n, callee.typ, bu, stmts)
          bu.subTree Addr:
            bu.add Node(kind: Local, val: tmp)

      # return the temporary as the expression
      bu.add Node(kind: Local, val: tmp)
    else:
      bu.subTree Call:
        c.useCallee(callee, bu, stmts)
        c.argsToIL(t, n, callee.typ, bu, stmts)

    result = callee.typ.elems[0]
  else:
    if callee.typ.kind != tkError: # don't cascade errors
      c.error("callee expression must be of procedural type")

    # analyze all arguments for errors and context side-effects
    for it in t.items(n, 1):
      discard c.exprToIL(t, it)

    # return an error
    bu.add Node(kind: IntVal)
    result = errorType()

proc callToIL(c; t; n: NodeIndex, bu; stmts): SemType =
  # first check whether its call to a built-in procedure (those take
  # precedence)
  let callee = t.child(n, 0)
  if t[callee].kind == Ident:
    let
      name = t.getString(callee)
      ent  = c.lookup(name)

    if ent.kind == ekBuiltinProc:
      case name
      of "+", "-":
        result = binaryArithToIL(c, t, n, name, bu, stmts)
      of "==", "<", "<=":
        result = relToIL(c, t, n, name, bu, stmts)
      of "not":
        result = notToIL(c, t, n, bu, stmts)
      else:
        unreachable()
      return

  # it must be a call to a user-defined procedure (or an error)
  result = userCallToIL(c, t, n, bu, stmts)

proc localDeclToIL(c; t; n: NodeIndex, bu, stmts) =
  ## Translates a procedure-local declaration to the target IL.
  let
    (npos, init) = t.pair(n)
    name = t.getString(npos)

  var e = c.exprToIL(t, init)
  if e.typ.kind == tkVoid:
    c.error("cannot initialize local with `void` expression")
    # turn into an error expression:
    e.typ = errorType()
    e.expr = @[Node(kind: IntVal)]

  let local = c.newTemp(e.typ)
  stmts.add e.stmts
  stmts.addStmt:
    c.genAsgn(Node(kind: Local, val: local), e.expr, e.typ, bu)

  # verify that the name isn't in use already *after* analyzing the
  # initializer; the expression could introduce an entity with the same name
  if c.lookup(name).kind != ekNone:
    c.error("redeclaration of " & name)
    # don't abort; override the existing entity for the sake of error
    # correction

  # register the declaration *after* analyzing the expression
  c.addDecl(name, Entity(kind: ekLocal, id: local.int))

proc exprToIL(c; t: InTree, n: NodeIndex, bu, stmts): ExprType =
  case t[n].kind
  of SourceKind.IntVal:
    bu.add Node(kind: IntVal, val: c.literals.pack(t.getInt(n)))
    result = prim(tkInt) + {}
  of SourceKind.FloatVal:
    bu.add Node(kind: FloatVal, val: c.literals.pack(t.getFloat(n)))
    result = prim(tkFloat) + {}
  of SourceKind.Ident:
    let
      name = t.getString(n)
      ent = c.lookup(name)
    case ent.kind
    of ekBuiltinVal:
      case name
      of "false":
        bu.add Node(kind: IntVal, val: 0)
        result = prim(tkBool) + {}
      of "true":
        bu.add Node(kind: IntVal, val: 1)
        result = prim(tkBool) + {}
    of ekLocal:
      bu.add Node(kind: Local, val: ent.id.uint32)
      result = c.locals[ent.id] + {Lvalue, Mutable}
    of ekParam:
      if c.params[ent.id].typ.kind in AggregateTypes:
        # aggregate parameters use pass-by-address
        bu.subTree Deref:
          bu.add Node(kind: Type, val: c.typeToIL(c.params[ent.id].typ))
          bu.subTree Copy:
            bu.add Node(kind: Local, val: c.params[ent.id].local)
      else:
        bu.add Node(kind: Local, val: c.params[ent.id].local)
      result = c.params[ent.id].typ + {Lvalue}
    of ekProc:
      # expand to a procedure address (`ProcVal`), which is always correct;
      # the callsite can turn it into a static reference (`Proc`) as needed
      bu.add Node(kind: ProcVal, val: ent.id.uint32)
      result = c.procList[ent.id].typ + {}
    of ekNone:
      c.error("undeclared identifier: " & t.getString(n))
      bu.add Node(kind: IntVal)
      result = prim(tkError) + {}
    else:
      c.error("'" & name & "' cannot be used in this context")
      bu.add Node(kind: IntVal)
      result = prim(tkError) + {}
  of SourceKind.And, SourceKind.Or:
    let
      (a, b) = t.pair(n)
      ea  = c.fitExprStrict(c.exprToIL(t, a), prim(tkBool))
      # the second operand is evaluated conditionally, and it's thus placed
      # within its own scope
      eb  = c.fitExprStrict(c.scopedExprToIL(t, b), prim(tkBool))
      tmp = c.newTemp(prim(tkBool))

    if t[n].kind == SourceKind.And:
      # (And a b) -> (If a b False)
      stmts.addStmt If:
        genUse(ea, bu, stmts)
        bu.subTree Stmts: # then branch
          bu.add eb.stmts
          bu.subTree Asgn:
            bu.add Node(kind: Local, val: tmp)
            genUse(eb.expr, bu)
        bu.subTree Asgn: # else branch
          bu.add Node(kind: Local, val: tmp)
          bu.add Node(kind: IntVal, val: c.literals.pack(0))

    else:
      # (Or a b) -> (If a True b)
      stmts.addStmt If:
        genUse(ea, bu, stmts)
        bu.subTree Asgn: # then branch
          bu.add Node(kind: Local, val: tmp)
          bu.add Node(kind: IntVal, val: c.literals.pack(1))
        bu.subTree Stmts: # else branch
          bu.add eb.stmts
          bu.subTree Asgn:
            bu.add Node(kind: Local, val: tmp)
            genUse(eb.expr, bu)

    bu.add Node(kind: Local, val: tmp)
    result = prim(tkBool) + {}
  of SourceKind.If:
    let
      (p, b) = t.pair(n) # predicate and body, always present
      cond = exprToIL(c, t, p)
    if cond.typ.kind != tkBool:
      c.error("`If` condition must be a boolean expression")

    let
      body = scopedExprToIL(c, t, b)
      els = if t.len(n) == 3: scopedExprToIL(c, t, t.child(n, 2))
            else:             unitExpr
      typ = commonType(body.typ, els.typ)
      (fb, fe) =
        case typ.kind
        of tkError:
          c.error("if ($1) and else ($2) branches cannot be unified into a single type" %
                  [$body.typ.kind, $els.typ.kind])
          (body, els)
        else:
          (c.fitExpr(body, typ), c.fitExpr(els, typ))
      tmp = c.newTemp(typ)

    stmts.addStmt If:
      genUse(cond, bu, stmts)
      bu.subTree Stmts:
        bu.add fb.stmts
        c.genAsgn(Node(kind: Local, val: tmp), fb.expr, fb.typ, bu)
      bu.subTree Stmts:
        bu.add fe.stmts
        c.genAsgn(Node(kind: Local, val: tmp), fe.expr, fe.typ, bu)
    genLocal(tmp, typ, bu)
    result = typ + {}
  of SourceKind.While:
    let (a, b) = t.pair(n)

    c.openScope()
    let
      cond = c.exprToIL(t, a)
      body = c.exprToIL(t, b)
    c.closeScope()

    if cond.typ.kind != tkBool:
      c.error("condition expression must be of type bool")

    if body.typ.kind notin {tkUnit, tkVoid}:
      c.error("`While` body must be a unit or void expression")

    stmts.addStmt Loop:
      bu.subTree Stmts:
        bu.add cond.stmts
        bu.subTree If:
          bu.subTree Not:
            genUse(cond.expr, bu)
          bu.subTree Break:
            bu.add Node(kind: Immediate, val: 1)

        bu.add body.stmts
        genDrop(body.expr, body.typ, bu)

    if t[a].kind == SourceKind.Ident and t.getString(a) == "true":
      # it's a loop that doesn't exit via non-exception control-flow
      stmts.addStmt Unreachable:
        discard
      result = prim(tkVoid) + {}
    else:
      bu.add UnitNode
      result = prim(tkUnit) + {}
  of SourceKind.Call:
    result = callToIL(c, t, n, bu, stmts) + {}
  of SourceKind.TupleCons:
    if t.len(n) > 0:
      var elems = newSeq[SemType](t.len(n))
      # there are no tuple constructors in the target IL; all elements are
      # assigned individually
      let tmp = Node(kind: Local, val: c.newTemp(errorType()))
      for i, it in t.pairs(n):
        let e = c.exprToIL(t, it)
        elems[i] = e.typ

        if e.typ.kind == tkError:
          return errorType() + {}
        elif e.typ.kind == tkVoid:
          c.error("tuple element cannot be 'void'")
          return errorType() + {}

        stmts.add e.stmts
        # add an assignment for the field:
        stmts.addStmt:
          let dest = buildTree Field:
            bu.add tmp
            bu.add Node(kind: Immediate, val: i.uint32)
          c.genAsgn(dest, e.expr, e.typ, bu)

      # now that we know the type, correct it:
      c.locals[tmp.val] = SemType(kind: tkTuple, elems: elems)

      bu.add tmp
      result = c.locals[tmp.val] + {}
    else:
      # it's the unit value
      bu.add UnitNode
      result = prim(tkUnit) + {}
  of SourceKind.FieldAccess:
    let
      (a, b) = t.pair(n)
      tup = c.exprToIL(t, a)
    case tup.typ.kind
    of tkTuple:
      let idx = t.getInt(b)
      if idx >= 0 and idx < tup.typ.elems.len:
        result = tup.typ.elems[idx] + tup.attribs
        bu.subTree Field:
          bu.inline(tup, stmts)
          bu.add Node(kind: Immediate, val: idx.uint32)
      else:
        c.error("tuple has no element with index " & $idx)
        result = errorType() + {Lvalue, Mutable}
    of tkError:
      result = tup.typ + {}
    else:
      c.error("expected 'tuple' value")
      result = errorType() + {}
  of SourceKind.Asgn:
    let (a, b) = t.pair(n)
    stmts.addStmt Asgn:
      # emit the destination expression in-place
      let dst = c.exprToIL(t, a, bu, stmts)
      if {Lvalue, Mutable} * dst.attribs < {Lvalue, Mutable}:
        c.error("LHS expression must be a mutable l-value expression")

      let src = c.fitExpr(c.exprToIL(t, b), dst.typ)
      stmts.add src.stmts
      genUse(src.expr, bu)

    bu.add UnitNode
    result = prim(tkUnit) + {}
  of SourceKind.Return:
    var e =
      case t.len(n)
      of 0: Expr(expr: @[Node(kind: IntVal)], typ: prim(tkUnit))
      of 1: c.exprToIL(t, t.child(n, 0))
      else: unreachable() # syntax error

    if e.typ.kind == tkVoid:
      c.error("cannot return 'void' expression")
      e.expr = @[Node(kind: IntVal)] # add a placholder
      e.typ = prim(tkError)

    # apply the necessary to-supertype conversions:
    e = c.fitExpr(e, c.retType)

    stmts.add e.stmts
    stmts.addStmt Return:
      case e.typ.kind
      of tkError:
        discard "do nothing"
      of AggregateTypes:
        # special handling for aggregate types: store through the out parameter
        stmts.addStmt Store:
          bu.add Node(kind: Type, val: c.typeToIL(e.typ))
          bu.subTree Copy:
            bu.add Node(kind: Local, val: c.returnParam)
          genUse(e.expr, bu)

        bu.add UnitNode # return the unitary value
      else:
        genUse(e.expr, bu)

    result = prim(tkVoid) + {}
  of SourceKind.Unreachable:
    stmts.addStmt Unreachable:
      discard
    result = prim(tkVoid) + {}
  of SourceKind.Exprs:
    let last = t.len(n) - 1
    var seenVoidExpr = false
    template voidGuard(body: untyped) =
      if not seenVoidExpr:
        body
    for i, si in t.pairs(n):
      let e = c.exprToIL(t, si)
      voidGuard:
        stmts.add e.stmts
      if i == last:
        voidGuard:
          result = e.typ + e.attribs
          case e.typ.kind
          of tkVoid: discard "okay, nothing to do"
          else:      bu.add e.expr
      else:
        case e.typ.kind
        of tkVoid:
          result = e.typ + e.attribs
          seenVoidExpr = true # check, but drop further stmts & exprs
        of tkUnit:
          voidGuard:
            stmts.addStmt:
              genDrop(e.expr, e.typ, bu)
        else:
          c.error("non-trailing expressions must be unit or void, got: $1" %
                    [$e.typ.kind])
          voidGuard:
            stmts.addStmt:
              genDrop(e.expr, e.typ, bu) # error correction
  of SourceKind.Decl:
    localDeclToIL(c, t, n, bu, stmts)
    bu.add UnitNode
    result = prim(tkUnit) + {}
  of AllNodes - ExprNodes:
    unreachable($t[n].kind)

proc open*(reporter: sink(ref ReportContext[string])): ModuleCtx =
  ## Creates a new empty module translation/analysis context.
  ModuleCtx(reporter: reporter,
            types: initBuilder[NodeKind](TypeDefs),
            procs: initBuilder[NodeKind](ProcDefs),
            scopes: @[default(Scope)]) # start with the top-level scope

proc close*(c: sink ModuleCtx): PackedTree[NodeKind] =
  ## Closes the module context and returns the accumulated translated code.
  var bu = initBuilder[NodeKind]()
  bu.subTree Module:
    bu.add finish(move c.types)
    bu.subTree GlobalDefs:
      discard
    bu.add finish(move c.procs)

  initTree[NodeKind](finish(bu), c.literals)

proc exprToIL*(c; t): SemType =
  ## Translates the given source language expression to the highest-level IL
  ## and turns it into a procedure. Also returns the type of the expression.
  var e = c.scopedExprToIL(t, NodeIndex(0))
  result = e.typ

  if e.typ.kind in AggregateTypes:
    # XXX: to properly handle non-primitive returns, the expression is
    #      currently analysed twice
    c.resetProcContext() # undo the effects
    c.locals.add prim(tkInt) # add the pointer parameter
    c.returnParam = 0
    c.retType = e.typ
    # crudely wrap the expression in a Return:
    let t =
      initTree(@[TreeNode[SourceKind](kind: SourceKind.Return, val: 1)] & t.nodes,
               t.literals)
    # analyse again:
    e = c.scopedExprToIL(t, NodeIndex(0))

  defer:
    c.resetProcContext()

  if result.kind == tkError:
    return # don't create any procedure

  let
    procTy    = procType(result)
    signature = c.genProcType(procTy)

  template bu: untyped = c.procs

  bu.subTree ProcDef:
    bu.add Node(kind: Type, val: signature)
    bu.subTree Locals:
      for it in c.locals.items:
        bu.add Node(kind: Type, val: c.typeToIL(it))
    bu.subTree Stmts:
      # first emit all statements:
      for it in e.stmts.items:
        bu.add it

      # then the expression:
      if e.typ.kind != tkVoid:
        bu.subTree Return:
          genUse(e.expr, bu)

  c.procList.add ProcInfo(typ: procType(result))

proc declToIL*(c; t; n: NodeIndex) =
  ## Translates the given source language declaration to the target IL.
  ## On success, the declaration effects are applied to `c` and the declared
  ## procedure's return type is returned.
  case t[n].kind
  of SourceKind.ProcDecl:
    let name = t.getString(t.child(n, 0))
    if c.lookup(name).kind != ekNone:
      c.error("redeclaration of '" & name & "'")
      return

    c.retType = evalType(c, t, t.child(n, 1))

    defer:
      c.resetProcContext() # clear the context again

    var procTy = procType(c.retType)

    # add the parameter types to the proc type:
    for it in t.items(t.child(n, 2)):
      procTy.elems.add c.expectNot(evalType(c, t, t.child(it, 1)), tkVoid)

    let signature = c.genProcType(procTy)

    # register the proc before analysing/translating the body
    c.procList.add ProcInfo(typ: procTy)
    c.addDecl(name, Entity(kind: ekProc, id: c.procList.high))

    c.openScope()
    # add the parameters to the scope:
    for i, it in t.pairs(t.child(n, 2)):
      let name = t.getString(t.child(it, 0))
      if c.lookup(name).kind != ekNone:
        c.error("redeclaration of '" & name & "'")

      # add the local and register the entity regadless of whether there was
      # an error
      if procTy.elems[i + 1].kind in AggregateTypes:
        c.locals.add pointerType # the parameter is of pointer type internally
      else:
        c.locals.add procTy.elems[i + 1]

      c.params.add (procTy.elems[i + 1], c.locals.high.uint32)
      c.addDecl(name, Entity(kind: ekParam, id: c.params.high))

    if c.retType.kind in AggregateTypes:
      # needs an extra pointer parameter
      c.locals.add prim(tkInt)
      c.returnParam = uint32(c.locals.len - 1)

    # analyse the body:
    let e = c.exprToIL(t, t.child(n, 3))
    c.closeScope()

    # the body expression must always be a void expression
    if e.typ.kind != tkVoid:
      c.error("a procedure body must be a 'void' expression")
      c.removeDecl(name) # remove again
      c.procList.del(c.procList.high)
      return

    var bu = initBuilder[NodeKind](ProcDef)
    bu.add Node(kind: Type, val: signature)
    bu.subTree Locals:
      for it in c.locals.items:
        bu.add Node(kind: Type, val: c.typeToIL(it))
    # add the body:
    bu.subTree Stmts:
      for it in e.stmts.items:
        bu.add it

    c.procs.add finish(bu)
  of SourceKind.TypeDecl:
    let name = t.getString(t.child(n, 0))
    if c.lookup(name).kind != ekNone:
      c.error("redeclaration of '" & name & "'")
      return

    let typ = evalType(c, t, t.child(n, 1))
    # add the type to the scope, regardless of whether `typ` is an error
    c.aliases.add typ
    c.addDecl(name, Entity(kind: ekType, id: c.aliases.high))
  of AllNodes - DeclNodes:
    unreachable() # syntax error
