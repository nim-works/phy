## This implements a temporary pass for translating the parse-tree of the
## source language into the currently highest-level intermediate language.
## It's there so that development of the source language can already commence
## while the the intermediate languages are still being developed.
##
## The focus is on correctness. Performance, code quality, and overall
## architecture (of this module) are of secondary concern.

import
  std/[sequtils, tables],
  passes/[builders, spec, trees],
  phy/[types],
  vm/[utils]

import passes/spec_source except NodeKind

type
  SourceKind = spec_source.NodeKind
  InTree     = PackedTree[SourceKind]
  Node       = TreeNode[NodeKind]
  NodeSeq    = seq[Node]

  ProcInfo = object
    id: int
      ## ID of the procedure
    result: SemType
      ## return type

  ModuleCtx* = object
    ## The translation/analysis context for a single module.
    literals: Literals
    types: Builder[NodeKind]
      ## the in-progress type section
    numTypes: int
    procs: Builder[NodeKind]
    numProcs: int

    scope: Table[string, ProcInfo]
      ## maps procedure names to their ID/position

    # procedure context:
    retType: SemType
    returnParam: uint32
      ## the index of the out parameter, if one is required
    locals: seq[SemType]
      ## all locals part of the procedure

  Expr = object
    # XXX: the target IL doesn't support expression lists (yet), so we have
    #      to apply the necessary lowering here, for now. Efficiency doesn't
    #      matter
    stmts: seq[NodeSeq] # can be empty
    expr: NodeSeq
    typ: SemType

using
  c: var ModuleCtx
  t: InTree
  bu: var Builder[NodeKind]
  stmts: var seq[NodeSeq]

template addType(c; kind: NodeKind, body: untyped): uint32 =
  c.types.subTree kind:
    body
  (let r = c.numTypes; inc c.numTypes; r.uint32)

proc evalType(t; n: NodeIndex): SemType =
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
        tup.elems.add evalType(t, it)
        if tup.elems[^1].kind in {tkError, tkVoid}:
          # error propagation and void handling
          tup = errorType()
          break

      tup
  else:       unreachable() # syntax error

proc typeToIL(c; typ: SemType): uint32 =
  case typ.kind
  of tkVoid:
    unreachable()
  of tkUnit:
    # XXX: there's no unit type in the target IL, and in order to not having
    #      to rewrite all ``unit`` type usages here, we're translating the
    #      type to a 1-byte integer
    c.addType Int: c.types.add(Node(kind: Immediate, val: 1))
  of tkBool:
    c.addType Int: c.types.add(Node(kind: Immediate, val: 1))
  of tkInt, tkError:
    c.addType Int: c.types.add(Node(kind: Immediate, val: 8))
  of tkFloat:
    c.addType Float: c.types.add(Node(kind: Immediate, val: 8))
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

proc genProcType(c; ret: SemType): uint32 =
  ## Generates a proc type with `ret` as the return type and adds it to `c`.
  case ret.kind
  of tkError:
    unreachable()
  of tkVoid:
    c.addType ProcTy:
      c.types.subTree Void: discard
  of ComplexTypes:
    # non-primitive types are passed via an out parameter.
    # ``() -> T`` becomes ``(int) -> unit``
    let
      ret = c.typeToIL(prim(tkUnit))
      arg = c.typeToIL(prim(tkInt))
    c.addType ProcTy:
      c.types.add Node(kind: Type, val: ret)
      c.types.add Node(kind: Type, val: arg)
  else:
    let typId = c.typeToIL(ret)
    c.addType ProcTy:
      c.types.add Node(kind: Type, val: typId)

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
  result = c.locals.len.uint32
  c.locals.add typ

proc genAsgn(c; a: Node|NodeSeq, b: NodeSeq, typ: SemType, bu) =
  ## Emits an ``a = b`` assignment to `bu`.
  case typ.kind
  of ComplexTypes:
    # complex types don't support assignments in the target IL, so a ``Copy``
    # has to be used
    # XXX: this will happen as part of a lowering pass, eventually
    bu.subTree Copy:
      bu.subTree Addr:
        bu.add a
      bu.subTree Addr:
        bu.add b
      bu.add Node(kind: IntVal, val: c.literals.pack(size(typ)))
  else:
    bu.subTree Asgn:
      bu.add a
      bu.add b

proc inline(bu; e: sink Expr; stmts) =
  ## Appends the trailing expression directly to `bu`.
  stmts.add e.stmts
  bu.add e.expr

proc capture(c; e: sink Expr; bu; stmts): Node =
  ## Commits expression `e` to a fresh temporary. This is part of the
  ## expression-list lowering machinery.
  let tmp = c.newTemp(e.typ)
  result = Node(kind: Local, val: tmp)

  stmts.add e.stmts
  stmts.addStmt:
    c.genAsgn(result, e.expr, e.typ, bu)

proc exprToIL(c; t: InTree, n: NodeIndex, bu, stmts): SemType

proc exprToIL(c; t: InTree, n: NodeIndex): Expr =
  var bu = initBuilder[NodeKind]()
  result.typ = exprToIL(c, t, n, bu, result.stmts)
  result.expr = finish(bu)

template lenCheck(t; n: NodeIndex, bu; expected: int) =
  ## Exits the current analysis procedure with an error, if `n` doesn't have
  ## `expected` children.
  if t.len(n) != expected:
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

  if eA.typ == eB.typ and eA.typ.kind in {tkInt, tkFloat}:
    let
      typ = c.typeToIL(eA.typ)
      a = c.capture(eA, bu, stmts)
      b = c.capture(eB, bu, stmts)

    bu.subTree op:
      bu.add Node(kind: Type, val: typ)
      bu.add a
      bu.add b

    result = eA.typ
  else:
    bu.add Node(kind: IntVal)
    result = errorType()

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
    let
      a = c.capture(eA, bu, stmts)
      b = c.capture(eB, bu, stmts)

    bu.subTree op:
      bu.add Node(kind: Type, val: c.typeToIL(eA.typ))
      bu.add a
      bu.add b

    result = prim(tkBool)
  else:
    bu.add Node(kind: IntVal)
    result = errorType()

proc notToIL(c; t; n: NodeIndex, bu; stmts): SemType =
  lenCheck(t, n, bu, 2)

  let arg = exprToIL(c, t, t.child(n, 1))

  if arg.typ.kind == tkBool:
    # a single argument, so no capture is necessary
    bu.subTree Not:
      bu.inline(arg, stmts)
    result = prim(tkBool)
  else:
    bu.add Node(kind: IntVal)
    result = errorType()

proc callToIL(c; t; n: NodeIndex, bu; stmts): SemType =
  let name = t.getString(t.child(n, 0))
  case name
  of "+", "-":
    result = binaryArithToIL(c, t, n, name, bu, stmts)
  of "==", "<", "<=":
    result = relToIL(c, t, n, name, bu, stmts)
  of "not":
    result = notToIL(c, t, n, bu, stmts)
  elif name in c.scope:
    # it's a user-defined procedure
    let prc {.cursor.} = c.scope[name]
    if t.len(n) == 1:
      # procedure arity is currently always 0
      case prc.result.kind
      of tkVoid:
        stmts.addStmt Call:
          bu.add Node(kind: Proc, val: prc.id.uint32)
        # mark the normal control-flow path as dead:
        bu.subTree Unreachable:
          discard
      of ComplexTypes:
        # the value is not returned normally, but passed via an out parameter
        let tmp = c.newTemp(prc.result)
        stmts.addStmt Call:
          bu.add Node(kind: Proc, val: prc.id.uint32)
          bu.subTree Addr:
            bu.add Node(kind: Local, val: tmp)

        # return the temporary as the expression
        bu.add Node(kind: Local, val: tmp)
      else:
        bu.subTree Call:
          bu.add Node(kind: Proc, val: prc.id.uint32)

      result = prc.result
    else:
      bu.add Node(kind: IntVal)
      result = errorType()
  else:
    bu.add Node(kind: IntVal)
    result = errorType()

proc exprToIL(c; t: InTree, n: NodeIndex, bu, stmts): SemType =
  case t[n].kind
  of SourceKind.IntVal:
    bu.add Node(kind: IntVal, val: c.literals.pack(t.getInt(n)))
    result = prim(tkInt)
  of SourceKind.FloatVal:
    bu.add Node(kind: FloatVal, val: c.literals.pack(t.getFloat(n)))
    result = prim(tkFloat)
  of SourceKind.Ident:
    case t.getString(n)
    of "false":
      bu.add Node(kind: IntVal, val: 0)
      result = prim(tkBool)
    of "true":
      bu.add Node(kind: IntVal, val: 1)
      result = prim(tkBool)
    else:
      bu.add Node(kind: IntVal)
      result = prim(tkError)
  of SourceKind.Call:
    result = callToIL(c, t, n, bu, stmts)
  of SourceKind.TupleCons:
    if t.len(n) > 0:
      var elems = newSeq[SemType](t.len(n))
      # there are no tuple constructors in the target IL; all elements are
      # assigned individually
      let tmp = Node(kind: Local, val: c.newTemp(errorType()))
      for i, it in t.pairs(n):
        let e = c.exprToIL(t, it)
        elems[i] = e.typ

        if e.typ.kind in {tkError, tkVoid}:
          return e.typ

        stmts.add e.stmts
        # add an assignment for the field:
        stmts.addStmt:
          let dest = buildTree Field:
            bu.add tmp
            bu.add Node(kind: Immediate, val: i.uint32)
          c.genAsgn(dest, e.expr, e.typ, bu)

      result = SemType(kind: tkTuple, elems: elems)
      # now that we know the type, correct it:
      c.locals[tmp.val] = result

      bu.add tmp
    else:
      # it's a unit value
      bu.add Node(kind: IntVal)
      result = prim(tkUnit)
  of SourceKind.Return:
    var typ: SemType
    bu.subTree Return:
      case t.len(n)
      of 0:
        # as long as it's an 8-bit integer, the exact value doesn't matter
        bu.add Node(kind: IntVal)
        typ = prim(tkUnit)
      of 1:
        let e = c.exprToIL(t, t.child(n, 0))
        typ = e.typ
        stmts.add e.stmts

        if e.typ.kind == tkError:
          return e.typ

        case e.typ.kind
        of ComplexTypes:
          # special handling for complex types; do a memcopy through the out
          # parameter
          stmts.addStmt Copy:
            bu.subTree Copy:
              bu.add Node(kind: Local, val: c.returnParam)
            bu.subTree Addr:
              bu.add e.expr
            bu.add Node(kind: IntVal, val: c.literals.pack(size(typ)))

          bu.add Node(kind: IntVal) # return the unitary value
        else:
          bu.add e.expr
      else:
        unreachable() # syntax error

    if typ.kind != tkVoid and typ == c.retType:
      result = prim(tkVoid)
    else:
      # TODO: use proper error correction; a return expression is always of
      #       type ``void``
      # type mismatch
      result = errorType()
  of SourceKind.Unreachable:
    bu.subTree Unreachable:
      discard
    result = prim(tkVoid)
  of AllNodes - ExprNodes:
    unreachable()

proc open*(): ModuleCtx =
  ## Creates a new empty module translation/analysis context.
  ModuleCtx(types: initBuilder[NodeKind](TypeDefs),
            procs: initBuilder[NodeKind](ProcDefs))

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
  var e = exprToIL(c, t, NodeIndex(0))
  result = e.typ

  if e.typ.kind in ComplexTypes:
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
    e = c.exprToIL(t, NodeIndex(0))

  defer:
    c.resetProcContext()

  if result.kind == tkError:
    return # don't create any procedure

  let procTy = c.genProcType(result)

  template bu: untyped = c.procs

  bu.subTree ProcDef:
    bu.add Node(kind: Type, val: procTy)
    bu.subTree Locals:
      for it in c.locals.items:
        bu.add Node(kind: Type, val: c.typeToIL(it))
    bu.subTree Stmts:
      # first emit all statements:
      for it in e.stmts.items:
        bu.add it

      # then the expression:
      case e.typ.kind
      of tkVoid:
        bu.add e.expr
      else:
        bu.subTree Return:
          bu.add e.expr

  inc c.numProcs

proc declToIL*(c; t; n: NodeIndex): SemType =
  ## Translates the given source language declaration to the target IL.
  ## On success, the declaration effects are applied to `c` and the declared
  ## procedure's return type is returned.
  case t[n].kind
  of SourceKind.ProcDecl:
    let name = t.getString(t.child(n, 0))
    if name in c.scope:
      # declaration with the given name already exists
      return errorType()

    c.retType = evalType(t, t.child(n, 1))

    let procTy = c.genProcType(c.retType)

    if c.retType.kind in ComplexTypes:
      # needs an extra pointer parameter
      c.locals.add prim(tkInt)
      c.returnParam = uint32(c.locals.len - 1)

    defer:
      c.resetProcContext() # clear the context again

    # register the proc before analysing/translating the body
    c.scope[name] = ProcInfo(id: c.numProcs, result: c.retType)

    let e = c.exprToIL(t, t.child(n, 3))
    # the body expression must always be a void expression
    if e.typ.kind != tkVoid:
      c.scope.del(name) # remove again
      return errorType()

    var bu = initBuilder[NodeKind](ProcDef)
    bu.add Node(kind: Type, val: procTy)
    bu.subTree Locals:
      for it in c.locals.items:
        bu.add Node(kind: Type, val: c.typeToIL(it))
    # add the body:
    bu.subTree Stmts:
      for it in e.stmts.items:
        bu.add it
      bu.add e.expr

    c.procs.add finish(bu)
    inc c.numProcs
    result = c.retType
  of AllNodes - DeclNodes:
    unreachable() # syntax error
