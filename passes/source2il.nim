## This implements a temporary pass for translating the parse-tree of the
## source language into the currently highest-level intermediate language.
## It's there so that development of the source language can already commence
## while the the intermediate languages are still being developed.
##
## The focus is on correctness. Performance, code quality, and overall
## architecture (of this module) are of secondary concern.

import
  std/[algorithm, sequtils, tables],
  passes/[builders, ir, spec, trees],
  phy/[reporting, types],
  vm/[utils]

from std/strutils import `%`

import passes/spec_source except NodeKind

type
  SourceKind = spec_source.NodeKind
  InTree     = PackedTree[SourceKind]
  Node       = TreeNode[NodeKind]

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
    stmts: seq[IrNode] # can be empty
    expr: IrNode
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

  UnitNode = IrNode(kind: IntVal, intVal: 0)
    ## the node representing the unitary value
  unitExpr = Expr(expr: UnitNode, typ: prim(tkUnit))
    ## the expression evaluating to the unitary value

  pointerType {.used.} = prim(tkInt)
    ## the type inhabited by pointer values. The constant is used as a
    ## placeholder until a dedicated pointer type is introduced

using
  c: var ModuleCtx
  t: InTree
  bu: var Builder[NodeKind]
  expr: var IrNode
  stmts: var seq[IrNode]

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
      # XXX: for the sake of ease of implementation, records use the maximum
      #      possible alignment
      c.types.add Node(kind: Immediate, val: 8)
      var off = 0 ## the current field offset
      for i, it in args.pairs:
        c.types.subTree Field:
          c.types.add Node(kind: Immediate, val: off.uint32)
          c.types.add Node(kind: Type, val: it)
        off += size(typ.elems[i])
  of tkUnion:
    let args = mapIt(typ.elems, c.typeToIL(it))
    let inner = c.addType Union:
      c.types.add Node(kind: Immediate, val: size(typ).uint32 - 8)
      c.types.add Node(kind: Immediate, val: 8)
      for it in args.items:
        c.types.add Node(kind: Type, val: it)

    let tag = c.typeToIL(prim(tkInt))
    c.addType Record:
      c.types.add Node(kind: Immediate, val: size(typ).uint32)
      # XXX: alignment is ignored at the moment and just set to 1
      c.types.add Node(kind: Immediate, val: 8)
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

func numILParams(typ: SemType): int =
  ## Returns the number of parameters the IL signature type generated from
  ## `typ` is going to have.
  assert typ.kind == tkProc
  typ.elems.len - 1

proc rawGenProcType(c; typ: SemType): uint32 =
  ## Generates the IL representation for the procedure signature type `typ`
  ## and adds it to `c`.
  assert typ.kind == tkProc
  let params = mapIt(typ.elems.toOpenArray(1, typ.elems.high)):
    c.typeToIL(it)

  template addParams() =
    for p in params.items:
      c.types.add Node(kind: Type, val: p)

  case typ.elems[0].kind
  of tkVoid:
    c.addType ProcTy:
      c.types.subTree Void: discard
      addParams()
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

proc resetProcContext(c) =
  c.locals.setLen(0) # re-use the memory

proc newTemp(c; typ: SemType): IrNode =
  ## Allocates a new temporary of `typ` type.
  case typ.kind
  of tkVoid:
    # do not create a temp for void
    result = IrNode(kind: None)
  else:
    result = newLocal(c.locals.len.uint32)
    c.locals.add typ

proc wrap(e: sink Expr, dest: IrNode): IrNode =
  ## Turns `e` into a statement list. The expression part is turned into an
  ## assignment to `dest`, but only if not a void expression.
  result = IrNode(kind: Stmts, children: e.stmts)
  if e.typ.kind != tkVoid:
    result.add newAsgn(dest, e.expr)

proc inline(e: sink Expr, stmts): IrNode =
  ## Adds the statement part of `e` to `stmts` and returns the expression part.
  stmts.add e.stmts
  e.expr

proc capture(c; e: sink Expr; stmts): IrNode =
  ## Commits expression `e` to a fresh temporary. This is part of the
  ## expression-list lowering machinery.
  result = c.newTemp(e.typ)
  stmts.add e.stmts
  stmts.add newAsgn(result, e.expr)

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
        result.stmts.add:
          newAsgn(newFieldExpr(tmp, 0), newIntVal(idx))
        # emit the value assignment:
        result.stmts.add:
          newAsgn(newFieldExpr(newFieldExpr(tmp, 1), idx), e.expr)

        result.expr = tmp
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
    result = Expr(stmts: e.stmts, typ: errorType())

proc fitExprStrict(c; e: sink Expr, typ: SemType): Expr =
  ## Makes sure expression `e` fits `typ` exactly, reporting an error and
  ## returning an error-expression if not.
  if e.typ == typ:
    result = e # all good
  else:
    c.error("expected expression of type $1 but got type $2" %
            [$typ.kind, $e.typ.kind])
    # turn into an error expression:
    result = Expr(stmts: e.stmts, typ: errorType())

proc exprToIL(c; t: InTree, n: NodeIndex, expr, stmts): ExprType

proc exprToIL(c; t: InTree, n: NodeIndex): Expr =
  result.expr = IrNode(kind: None)
  (result.typ, result.attribs) = exprToIL(c, t, n, result.expr, result.stmts)
  # verify some postconditions:
  assert result.typ.kind != tkVoid or result.expr.kind == None,
         "void `Expr` cannot have a trailing expression"
  assert result.typ.kind in {tkVoid, tkError} or result.expr.kind != None,
         "non-void `Expr` must have a trailing expression"

proc scopedExprToIL(c; t; n: NodeIndex): Expr =
  ## Analyzes the given expression and generates the IL for it. Analysis
  ## happens within a new scope, which is discarded afterwards.
  c.openScope()
  result = c.exprToIL(t, n)
  c.closeScope()

template lenCheck(t; n: NodeIndex, expected: int) =
  ## Exits the current analysis procedure with an error, if `n` doesn't have
  ## `expected` children.
  if t.len(n) != expected:
    c.error("expected " & $expected & " arguments, but got " & $t.len(n))
    return errorType()

proc binaryArithToIL(c; t; n: NodeIndex, name: string, expr, stmts): SemType =
  ## Analyzes and emits the IL for a binary arithmetic operation.
  lenCheck(t, n, 3)

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
    expr = newBinaryOp(op, c.typeToIL(eA.typ),
                       c.capture(eA, stmts),
                       c.capture(eB, stmts))
    result = eA.typ

proc relToIL(c; t; n: NodeIndex, name: string, expr; stmts): SemType =
  ## Analyzes and emits the IL for a relational operation.
  lenCheck(t, n, 3)

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
    expr = newBinaryOp(op, c.typeToIL(eA.typ),
                       c.capture(eA, stmts),
                       c.capture(eB, stmts))
    result = prim(tkBool)
  elif tkError in {eA.typ.kind, eB.typ.kind}:
    result = errorType()
  else:
    c.error("arguments have mismatching types")
    result = errorType()

proc notToIL(c; t; n: NodeIndex, expr; stmts): SemType =
  lenCheck(t, n, 2)

  let arg = exprToIL(c, t, t.child(n, 1))

  if arg.typ.kind == tkBool:
    # a single argument, so no capture is necessary
    expr = newNot(inline(arg, stmts))
    result = prim(tkBool)
  else:
    c.error("expected 'bool' expression")
    result = errorType()

proc userCallToIL(c; t; n: NodeIndex, expr; stmts): SemType =
  ## Analyzes a non-built-in call expression and translates it to its IL
  ## representation.
  let callee = c.exprToIL(t, t.child(n, 0))

  if callee.typ.kind == tkProc:
    proc addArgs(call: var IrNode, c; t; n: NodeIndex; prc: SemType; stmts
                ) {.nimcall.} =
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
        call.add tmp

        inc i

      if i != prc.elems.len:
        # arity mismatch
        c.error("expected $1 arguments but got $2" %
                [$(prc.elems.len - 1), $(i - 1)])

    stmts.add callee.stmts

    var call = IrNode(kind: Call)
    if callee.expr.kind == Proc:
      # the callee is a statically-known procedure; it's a static call
      call.add callee.expr
    else:
      call.add IrNode(kind: Type, id: c.genProcType(callee.typ))
      call.add callee.expr

    call.addArgs(c, t, n, callee.typ, stmts)

    # some return types need special handling
    case callee.typ.elems[0].kind
    of tkVoid:
      stmts.add call
      # mark the non-exceptional call exit as unreachable:
      stmts.add newUnreachable()
    else:
      expr = call

    result = callee.typ.elems[0]
  else:
    if callee.typ.kind != tkError: # don't cascade errors
      c.error("callee expression must be of procedural type")

    # analyze all arguments for errors and context side-effects
    for it in t.items(n, 1):
      discard c.exprToIL(t, it)

    # return an error
    result = errorType()

proc callToIL(c; t; n: NodeIndex, expr; stmts): SemType =
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
        result = binaryArithToIL(c, t, n, name, expr, stmts)
      of "==", "<", "<=":
        result = relToIL(c, t, n, name, expr, stmts)
      of "not":
        result = notToIL(c, t, n, expr, stmts)
      else:
        unreachable()
      return

  # it must be a call to a user-defined procedure (or an error)
  result = userCallToIL(c, t, n, expr, stmts)

proc localDeclToIL(c; t; n: NodeIndex, stmts) =
  ## Translates a procedure-local declaration to the target IL.
  let
    (npos, init) = t.pair(n)
    name = t.getString(npos)

  var e = c.exprToIL(t, init)
  if e.typ.kind == tkVoid:
    c.error("cannot initialize local with `void` expression")
    # turn into an error expression:
    e.typ = errorType()
    e.expr = IrNode(kind: None)

  let local = c.newTemp(e.typ)
  stmts.add newAsgn(local, inline(e, stmts))

  # verify that the name isn't in use already *after* analyzing the
  # initializer; the expression could introduce an entity with the same name
  if c.lookup(name).kind != ekNone:
    c.error("redeclaration of " & name)
    # don't abort; override the existing entity for the sake of error
    # correction

  # register the declaration *after* analyzing the expression
  c.addDecl(name, Entity(kind: ekLocal, id: local.id.int))

proc exprToIL(c; t: InTree, n: NodeIndex, expr, stmts): ExprType =
  case t[n].kind
  of SourceKind.IntVal:
    expr = newIntVal(t.getInt(n))
    result = prim(tkInt) + {}
  of SourceKind.FloatVal:
    expr = newFloatVal(t.getFloat(n))
    result = prim(tkFloat) + {}
  of SourceKind.Ident:
    let
      name = t.getString(n)
      ent = c.lookup(name)
    case ent.kind
    of ekBuiltinVal:
      case name
      of "false":
        expr = newIntVal(0)
        result = prim(tkBool) + {}
      of "true":
        expr = newIntVal(1)
        result = prim(tkBool) + {}
    of ekLocal:
      expr = newLocal(ent.id.uint32)
      result = c.locals[ent.id] + {Lvalue, Mutable}
    of ekParam:
      expr = newLocal(c.params[ent.id].local)
      result = c.params[ent.id].typ + {Lvalue}
    of ekProc:
      # expand to a procedure address (`ProcVal`), which is always correct;
      # the callsite can turn it into a static reference (`Proc`) as needed
      expr = IrNode(kind: Proc, id: ent.id.uint32)
      result = c.procList[ent.id].typ + {}
    of ekNone:
      c.error("undeclared identifier: " & t.getString(n))
      result = prim(tkError) + {}
    else:
      c.error("'" & name & "' cannot be used in this context")
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
      stmts.add newIf(inline(ea, stmts),
                      wrap(eb, tmp),
                      newAsgn(tmp, newIntVal(0)))

    else:
      # (Or a b) -> (If a True b)
      stmts.add newIf(inline(ea, stmts),
                      newAsgn(tmp, newIntVal(1)),
                      wrap(eb, tmp))

    expr = tmp
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

    stmts.add newIf(inline(cond, stmts), wrap(fb, tmp), wrap(fe, tmp))
    expr = tmp
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

    var sub = IrNode(kind: Stmts)
    sub.add cond.stmts
    sub.add newIf(newNot(cond.expr), newBreak(1))
    sub.add body.stmts
    if body.typ.kind != tkVoid:
      sub.add newDrop(body.expr)

    stmts.add IrNode(kind: Loop, children: @[sub])

    if t[a].kind == SourceKind.Ident and t.getString(a) == "true":
      # it's a loop that doesn't exit via non-exception control-flow
      stmts.add newUnreachable()
      result = prim(tkVoid) + {}
    else:
      expr = UnitNode
      result = prim(tkUnit) + {}
  of SourceKind.Call:
    result = callToIL(c, t, n, expr, stmts) + {}
  of SourceKind.TupleCons:
    if t.len(n) > 0:
      var elems = newSeq[SemType](t.len(n))
      # there are no tuple constructors in the target IL; all elements are
      # assigned individually
      let tmp = c.newTemp(errorType())
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
        stmts.add newAsgn(newFieldExpr(tmp, i), e.expr)

      # now that we know the type, correct it:
      c.locals[tmp.id] = SemType(kind: tkTuple, elems: elems)

      expr = tmp
      result = c.locals[tmp.id] + {}
    else:
      # it's the unit value
      expr = UnitNode
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
        expr = newFieldExpr(inline(tup, stmts), idx.int)
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
    var dst = c.exprToIL(t, a)
    if {Lvalue, Mutable} * dst.attribs < {Lvalue, Mutable}:
      c.error("LHS expression must be a mutable l-value expression")
      dst.expr = IrNode(kind: None)

    let src = c.fitExpr(c.exprToIL(t, b), dst.typ)
    stmts.add newAsgn(inline(dst, stmts), inline(src, stmts))

    expr = UnitNode
    result = prim(tkUnit) + {}
  of SourceKind.Return:
    var e =
      case t.len(n)
      of 0: unitExpr
      of 1: c.exprToIL(t, t.child(n, 0))
      else: unreachable() # syntax error

    if e.typ.kind == tkVoid:
      c.error("cannot return 'void' expression")
      e.typ = prim(tkError)

    # apply the necessary to-supertype conversions:
    e = c.fitExpr(e, c.retType)

    stmts.add e.stmts
    case e.typ.kind
    of tkError:
      discard "do nothing"
    else:
      stmts.add newReturn(e.expr)

    result = prim(tkVoid) + {}
  of SourceKind.Unreachable:
    stmts.add newUnreachable()
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
          else:      expr = e.expr
      else:
        case e.typ.kind
        of tkVoid:
          result = e.typ + e.attribs
          seenVoidExpr = true # check, but drop further stmts & exprs
        of tkUnit:
          voidGuard:
            stmts.add newDrop(e.expr)
        else:
          c.error("non-trailing expressions must be unit or void, got: $1" %
                    [$e.typ.kind])
          voidGuard:
            stmts.add newDrop(e.expr) # error correction
  of SourceKind.Decl:
    localDeclToIL(c, t, n, stmts)
    expr = UnitNode
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
    bu.subTree Params:
      for i in 0..<numILParams(procTy):
        bu.add Node(kind: Local, val: i.uint32)
    bu.subTree Locals:
      for it in c.locals.items:
        bu.add Node(kind: Type, val: c.typeToIL(it))
    bu.subTree Stmts:
      # first emit all statements:
      for it in e.stmts.items:
        convert(it, c.literals, bu)

      # then the expression:
      if e.typ.kind != tkVoid:
        bu.subTree Return:
          use(e.expr, c.literals, bu)

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
      c.locals.add procTy.elems[i + 1]

      c.params.add (procTy.elems[i + 1], c.locals.high.uint32)
      c.addDecl(name, Entity(kind: ekParam, id: c.params.high))

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
    bu.subTree Params:
      for i in 0..<numILParams(procTy):
        bu.add Node(kind: Local, val: i.uint32)
    bu.subTree Locals:
      for it in c.locals.items:
        bu.add Node(kind: Type, val: c.typeToIL(it))
    # add the body:
    bu.subTree Stmts:
      for it in e.stmts.items:
        convert(it, c.literals, bu)

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
