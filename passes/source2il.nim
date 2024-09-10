## This implements a temporary pass for translating the parse-tree of the
## source language into the currently highest-level intermediate language.
## It's there so that development of the source language can already commence
## while the the intermediate languages are still being developed.
##
## The focus is on correctness. Performance, code quality, and overall
## architecture (of this module) are of secondary concern.

import
  std/[tables],
  passes/[builders, spec, trees],
  vm/[utils]

import passes/spec_source except NodeKind

type
  SourceKind = spec_source.NodeKind
  InTree     = PackedTree[SourceKind]
  Node       = TreeNode[NodeKind]
  NodeSeq    = seq[Node]

  TypeKind* = enum
    tkError
    tkVoid
    tkUnit
    tkBool
    tkInt
    tkFloat

  ProcInfo = object
    id: int
      ## ID of the procedure
    result: TypeKind
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
    retType: TypeKind

using
  c: var ModuleCtx
  t: InTree
  bu: var Builder[NodeKind]

template addType(c; kind: NodeKind, body: untyped): uint32 =
  c.types.subTree kind:
    body
  (let r = c.numTypes; inc c.numTypes; r.uint32)

proc parseType(t; n: NodeIndex): TypeKind =
  case t[n].kind
  of UnitTy:  tkUnit
  of BoolTy:  tkBool
  of IntTy:   tkInt
  of FloatTy: tkFloat
  else:       unreachable() # syntax error

proc typeToIL(c; typ: TypeKind): uint32 =
  case typ
  of tkVoid, tkUnit:
    unreachable()
  of tkBool:
    c.addType Int: c.types.add(Node(kind: Immediate, val: 1))
  of tkInt, tkError:
    c.addType Int: c.types.add(Node(kind: Immediate, val: 8))
  of tkFloat:
    c.addType Float: c.types.add(Node(kind: Immediate, val: 8))

proc genProcType(c; ret: TypeKind): uint32 =
  ## Generates a proc type with `ret` as the return type and adds it to `c`.
  case ret
  of tkError:
    unreachable()
  of tkVoid, tkUnit:
    # a ``void`` return type means "doesn't return a value", and since there's
    # only a single value for the ``unit`` type, it too maps to the void
    # return type
    c.addType ProcTy:
      c.types.subTree Void: discard
  else:
    let typId = c.typeToIL(ret)
    c.addType ProcTy:
      c.types.add Node(kind: Type, val: typId)

proc exprToIL(c; t: InTree, n: NodeIndex, bu): TypeKind

proc exprToIL(c; t: InTree, n: NodeIndex): (NodeSeq, TypeKind) =
  var bu = initBuilder[NodeKind]()
  result[1] = exprToIL(c, t, n, bu)
  result[0] = finish(bu)

template lenCheck(t; n: NodeIndex, bu; expected: int) =
  ## Exits the current analysis procedure with an error, if `n` doesn't have
  ## `expected` children.
  if t.len(n) != expected:
    bu.add Node(kind: IntVal)
    return tkError

proc binaryArithToIL(c; t; n: NodeIndex, name: string, bu): TypeKind =
  ## Analyzes and emits the IL for a binary arithmetic operation.
  lenCheck(t, n, bu, 3)

  let
    (_, a, b)  = t.triplet(n)
    (eA, typA) = exprToIL(c, t, a)
    (eB, typB) = exprToIL(c, t, b)

  let op =
    case name
    of "+": Add
    of "-": Sub
    else:   unreachable()

  if typA == typB and typA in {tkInt, tkFloat}:
    let typ = c.typeToIL(typA)

    bu.subTree op:
      bu.add Node(kind: Type, val: typ)
      bu.add eA
      bu.add eB

    result = typA
  else:
    bu.add Node(kind: IntVal)
    result = tkError

proc relToIL(c; t; n: NodeIndex, name: string, bu): TypeKind =
  ## Analyzes and emits the IL for a relational operation.
  lenCheck(t, n, bu, 3)

  let
    (_, a, b)  = t.triplet(n)
    (eA, typA) = exprToIL(c, t, a)
    (eB, typB) = exprToIL(c, t, b)

  let (op, valid) =
    case name
    of "==": (Eq, {tkBool, tkInt, tkFloat})
    of "<":  (Lt, {tkInt, tkFloat})
    of "<=": (Le, {tkInt, tkFloat})
    else:   unreachable()

  if typA == typB and typA in valid:
    bu.subTree op:
      bu.add Node(kind: Type, val: c.typeToIL(typA))
      bu.add eA
      bu.add eB

    result = tkBool
  else:
    bu.add Node(kind: IntVal)
    result = tkError

proc notToIL(c; t; n: NodeIndex, bu): TypeKind =
  lenCheck(t, n, bu, 2)

  let (arg, typ) = exprToIL(c, t, t.child(n, 1))

  if typ == tkBool:
    bu.subTree Not:
      bu.add arg
    result = tkBool
  else:
    bu.add Node(kind: IntVal)
    result = tkError

proc callToIL(c; t; n: NodeIndex, bu): TypeKind =
  let name = t.getString(t.child(n, 0))
  case name
  of "+", "-":
    result = binaryArithToIL(c, t, n, name, bu)
  of "==", "<", "<=":
    result = relToIL(c, t, n, name, bu)
  of "not":
    result = notToIL(c, t, n, bu)
  else:
    bu.add Node(kind: IntVal)
    result = tkError

proc exprToIL(c; t: InTree, n: NodeIndex, bu): TypeKind =
  case t[n].kind
  of SourceKind.IntVal:
    bu.add Node(kind: IntVal, val: c.literals.pack(t.getInt(n)))
    result = tkInt
  of SourceKind.FloatVal:
    bu.add Node(kind: FloatVal, val: c.literals.pack(t.getFloat(n)))
    result = tkFloat
  of SourceKind.Ident:
    case t.getString(n)
    of "false":
      bu.add Node(kind: IntVal, val: 0)
      result = tkBool
    of "true":
      bu.add Node(kind: IntVal, val: 1)
      result = tkBool
    else:
      bu.add Node(kind: IntVal)
      result = tkError
  of SourceKind.Call:
    result = callToIL(c, t, n, bu)
  of SourceKind.Return:
    var typ: TypeKind
    bu.subTree Return:
      typ =
        case t.len(n)
        of 0: tkUnit
        of 1: exprToIL(c, t, t.child(n, 0), bu)
        else: unreachable() # syntax error

    if typ != tkError and typ == c.retType:
      result = tkVoid
    else:
      # TODO: use proper error correction; a return expression is always of
      #       type ``void``
      # type mismatch
      result = tkError
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

proc exprToIL*(c; t): TypeKind =
  ## Translates the given source language expression to the highest-level IL
  ## and turns it into a procedure. Also returns the type of the expression.
  let (e, typ) = exprToIL(c, t, NodeIndex(0))
  if typ == tkError:
    return tkError # don't create any procedure

  let procTy = c.genProcType(typ)

  template bu: untyped = c.procs

  bu.subTree ProcDef:
    bu.add Node(kind: Type, val: procTy)
    bu.subTree Locals: discard
    case typ
    of tkVoid:
      bu.add e
    of tkUnit:
      bu.subTree Stmts:
        bu.add e
        bu.subTree Return:
          discard
    else:
      bu.subTree Return:
        bu.add e

  inc c.numProcs
  result = typ

proc declToIL*(c; t; n: NodeIndex): TypeKind =
  ## Translates the given source language declaration to the target IL.
  ## On success, the declaration effects are applied to `c` and the declared
  ## procedure's return type is returned.
  case t[n].kind
  of SourceKind.ProcDecl:
    let name = t.getString(t.child(n, 0))
    if name in c.scope:
      # declaration with the given name already exists
      return tkError

    c.retType = parseType(t, t.child(n, 1))

    let procTy = c.genProcType(c.retType)

    var bu = initBuilder[NodeKind](ProcDef)
    bu.add Node(kind: Type, val: procTy)
    bu.subTree Locals:
      discard

    # register the proc before analysing/translating the body
    c.scope[name] = ProcInfo(id: c.numProcs, result: c.retType)

    let (e, eTyp) = c.exprToIL(t, t.child(n, 3))
    if eTyp == tkVoid:
      # the expression must always be a void expression
      bu.add e
    else:
      c.scope.del(name) # remove again
      return tkError

    c.procs.add finish(bu)
    inc c.numProcs
    result = c.retType
  of AllNodes - DeclNodes:
    unreachable() # syntax error
