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

using
  c: var ModuleCtx
  t: InTree
  bu: var Builder[NodeKind]

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
  else:
    let typId = c.typeToIL(ret)
    c.addType ProcTy:
      c.types.add Node(kind: Type, val: typId)

proc exprToIL(c; t: InTree, n: NodeIndex, bu): SemType

proc exprToIL(c; t: InTree, n: NodeIndex): (NodeSeq, SemType) =
  var bu = initBuilder[NodeKind]()
  result[1] = exprToIL(c, t, n, bu)
  result[0] = finish(bu)

template lenCheck(t; n: NodeIndex, bu; expected: int) =
  ## Exits the current analysis procedure with an error, if `n` doesn't have
  ## `expected` children.
  if t.len(n) != expected:
    bu.add Node(kind: IntVal)
    return errorType()

proc binaryArithToIL(c; t; n: NodeIndex, name: string, bu): SemType =
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

  if typA == typB and typA.kind in {tkInt, tkFloat}:
    let typ = c.typeToIL(typA)

    bu.subTree op:
      bu.add Node(kind: Type, val: typ)
      bu.add eA
      bu.add eB

    result = typA
  else:
    bu.add Node(kind: IntVal)
    result = errorType()

proc relToIL(c; t; n: NodeIndex, name: string, bu): SemType =
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

  if typA == typB and typA.kind in valid:
    bu.subTree op:
      bu.add Node(kind: Type, val: c.typeToIL(typA))
      bu.add eA
      bu.add eB

    result = prim(tkBool)
  else:
    bu.add Node(kind: IntVal)
    result = errorType()

proc notToIL(c; t; n: NodeIndex, bu): SemType =
  lenCheck(t, n, bu, 2)

  let (arg, typ) = exprToIL(c, t, t.child(n, 1))

  if typ.kind == tkBool:
    bu.subTree Not:
      bu.add arg
    result = prim(tkBool)
  else:
    bu.add Node(kind: IntVal)
    result = errorType()

proc callToIL(c; t; n: NodeIndex, bu): SemType =
  let name = t.getString(t.child(n, 0))
  case name
  of "+", "-":
    result = binaryArithToIL(c, t, n, name, bu)
  of "==", "<", "<=":
    result = relToIL(c, t, n, name, bu)
  of "not":
    result = notToIL(c, t, n, bu)
  elif name in c.scope:
    # it's a user-defined procedure
    let prc {.cursor.} = c.scope[name]
    if t.len(n) == 1:
      # procedure arity is currently always 0
      case prc.result.kind
      of tkVoid:
        bu.subTree Stmts:
          bu.subTree Call:
            bu.add Node(kind: Proc, val: prc.id.uint32)
          # mark the normal control-flow path as dead:
          bu.subTree Unreachable:
            discard
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

proc exprToIL(c; t: InTree, n: NodeIndex, bu): SemType =
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
    result = callToIL(c, t, n, bu)
  of SourceKind.Return:
    var typ: SemType
    bu.subTree Return:
      typ =
        case t.len(n)
        of 0:
          # as long as it's an 8-bit integer, the exact value doesn't matter
          bu.add Node(kind: IntVal)
          prim(tkUnit)
        of 1: exprToIL(c, t, t.child(n, 0), bu)
        else: unreachable() # syntax error

    if typ.kind notin {tkError, tkVoid} and typ == c.retType:
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
  let (e, typ) = exprToIL(c, t, NodeIndex(0))
  if typ.kind == tkError:
    return typ # don't create any procedure

  let procTy = c.genProcType(typ)

  template bu: untyped = c.procs

  bu.subTree ProcDef:
    bu.add Node(kind: Type, val: procTy)
    bu.subTree Locals: discard
    case typ.kind
    of tkVoid:
      bu.add e
    else:
      bu.subTree Return:
        bu.add e

  inc c.numProcs
  result = typ

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

    var bu = initBuilder[NodeKind](ProcDef)
    bu.add Node(kind: Type, val: procTy)
    bu.subTree Locals:
      discard

    # register the proc before analysing/translating the body
    c.scope[name] = ProcInfo(id: c.numProcs, result: c.retType)

    let (e, eTyp) = c.exprToIL(t, t.child(n, 3))
    if eTyp.kind == tkVoid:
      # the expression must always be a void expression
      bu.add e
    else:
      c.scope.del(name) # remove again
      return errorType()

    c.procs.add finish(bu)
    inc c.numProcs
    result = c.retType
  of AllNodes - DeclNodes:
    unreachable() # syntax error
