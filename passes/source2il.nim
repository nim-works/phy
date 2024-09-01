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

proc exprToIL(c; t: InTree, n: NodeIndex, bu): TypeKind

proc exprToIL(c; t: InTree, n: NodeIndex): (NodeSeq, TypeKind) =
  var bu = initBuilder[NodeKind]()
  result[1] = exprToIL(c, t, n, bu)
  result[0] = finish(bu)

proc binaryArithToIL(c; t; n: NodeIndex, name: string, bu): TypeKind =
  ## Analyzes and emits the IL for a binary arithmetic call.
  if t.len(n) != 3:
    bu.add Node(kind: IntVal, val: 0) # add at least something
    return tkError

  let
    (_, a, b)  = t.triplet(n)
    (eA, typA) = exprToIL(c, t, a)
    (eB, typB) = exprToIL(c, t, b)

  let op =
    case name
    of "+": Add
    of "-": Sub
    else:   unreachable()

  if typA == typB and typA != tkError:
    let typ =
      if typA == tkInt:
        c.addType Int:
          c.types.add Node(kind: Immediate, val: 8)
      else:
        c.addType Float:
          c.types.add Node(kind: Immediate, val: 8)

    bu.subTree op:
      bu.add Node(kind: Type, val: typ)
      bu.add eA
      bu.add eB

    result = typA
  else:
    bu.add Node(kind: IntVal)
    result = tkError

proc callToIL(c; t; n: NodeIndex, bu): TypeKind =
  let name = t.getString(t.child(n, 0))
  case name
  of "+", "-":
    result = binaryArithToIL(c, t, n, name, bu)
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
    typId =
      case typ
      of tkInt, tkError:
        c.addType Int: c.types.add(Node(kind: Immediate, val: 8))
      of tkFloat:
        c.addType Float: c.types.add(Node(kind: Immediate, val: 8))

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
        bu.subTree Continuations:
          bu.subTree Continuation:
            bu.subTree Params: discard
            bu.subTree Locals: discard
            bu.subTree Continue:
              bu.add Node(kind: Immediate, val: 1)
              # the expression is placed as an argument to the Continue:
              bu.add e

          bu.subTree Continuation:
            bu.subTree Params:
              bu.add Node(kind: Type, val: typId)

  result = (typ, initTree(bu.finish(), t.literals))
