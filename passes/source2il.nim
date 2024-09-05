## This implements a temporary pass for translating the parse-tree of the
## source language into the currently highest-level intermediate language.
## It's there so that development of the source language can already commence
## while the the intermediate languages are still being developed.
##
## The focus is on correctness. Performance, code quality, and overall
## architecture (of this module) are of secondary concern.

import
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
    tkBool
    tkInt
    tkFloat

  Context = object
    types: Builder[NodeKind]
      ## the in-progress type section
    numTypes: int

using
  c: var Context
  t: InTree
  bu: var Builder[NodeKind]

template addType(c; kind: NodeKind, body: untyped): uint32 =
  c.types.subTree kind:
    body
  (let r = c.numTypes; inc c.numTypes; r.uint32)

proc typeToIL(c; typ: TypeKind): uint32 =
  case typ
  of tkBool:
    c.addType Int: c.types.add(Node(kind: Immediate, val: 1))
  of tkInt, tkError:
    c.addType Int: c.types.add(Node(kind: Immediate, val: 8))
  of tkFloat:
    c.addType Float: c.types.add(Node(kind: Immediate, val: 8))

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
    bu.add Node(kind: IntVal, val: t[n].val)
    result = tkInt
  of SourceKind.FloatVal:
    bu.add Node(kind: FloatVal, val: t[n].val)
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
  of AllNodes - ExprNodes:
    unreachable()

proc exprToIL*(t: InTree): (TypeKind, PackedTree[NodeKind]) =
  ## Translates the given source language expression to the highest-level IL.
  ## Also returns the type of the expression.
  var c = Context(types: initBuilder[NodeKind](TypeDefs))

  let
    (e, typ) = exprToIL(c, t, NodeIndex(0))
    typId = c.typeToIL(typ)

    ptypId = c.addType ProcTy:
      c.types.add Node(kind: Type, val: typId)

  var bu = initBuilder[NodeKind]()
  bu.subTree Module:
    bu.add finish(move c.types)

    bu.subTree GlobalDefs:
      discard

    bu.subTree ProcDefs:
      bu.subTree ProcDef:
        bu.add Node(kind: Type, val: ptypId)
        bu.subTree Locals: discard
        bu.subTree Return:
          bu.add e

  result = (typ, initTree(bu.finish(), t.literals))
