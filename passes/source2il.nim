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

from passes/spec_source import nil

type
  SourceKind = spec_source.NodeKind
  InTree     = PackedTree[SourceKind]
  Node       = TreeNode[NodeKind]

  TypeKind* = enum
    tkInt
    tkFloat

using
  bu: var Builder[NodeKind]

proc exprToIL(t: InTree, n: NodeIndex, bu): TypeKind =
  case t[n].kind
  of SourceKind.IntVal:
    bu.add Node(kind: IntVal, val: t[n].val)
    result = tkInt
  of SourceKind.FloatVal:
    bu.add Node(kind: FloatVal, val: t[n].val)
    result = tkFloat
  of spec_source.AllNodes - spec_source.ExprNodes:
    unreachable()

proc exprToIL*(t: InTree): (TypeKind, PackedTree[NodeKind]) =
  ## Translates the given source language expression to the highest-level IL.
  ## Also returns the type of the expression.
  var typ: TypeKind
  block:
    # we need to know the type of the expression, so we translate the
    # expression using a temporary builder first
    var bu = initBuilder[NodeKind]()
    bu.subTree Module:
      typ = exprToIL(t, NodeIndex(0), bu)
    # XXX: this is bad. The Changeset/Builder API needs to support
    #      placeholders, where one can insert placeholders, with the
    #      actual subtree being created separately

  var bu = initBuilder[NodeKind]()

  bu.subTree Module:
    bu.subTree TypeDefs:
      case typ
      of tkInt:
        bu.subTree Int:
          bu.add Node(kind: Immediate, val: 8)
      else:
        bu.subTree Float:
          bu.add Node(kind: Immediate, val: 8)

      bu.subTree ProcTy:
        bu.add Node(kind: Type, val: 0)

    bu.subTree GlobalDefs:
      discard

    bu.subTree ProcDefs:
      bu.subTree ProcDef:
        bu.add Node(kind: Type, val: 1)
        bu.subTree Locals: discard
        bu.subTree Continuations:
          bu.subTree Continuation:
            bu.subTree Params: discard
            bu.subTree Locals: discard
            bu.subTree Continue:
              bu.add Node(kind: Immediate, val: 1)
              # the actual expression is placed as a parameter to the Continue:
              discard exprToIL(t, NodeIndex(0), bu)

          bu.subTree Continuation:
            bu.subTree Params:
              bu.add Node(kind: Type, val: 0)

  result = (typ, initTree(bu.finish(), t.literals))
