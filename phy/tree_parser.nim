## Implements an S-expression to `PackedTree <trees.html#PackedTree>`_ parser.

import
  passes/[trees],
  experimental/[sexp, sexp_parse]

proc fromSexp[T](n: SexpNode, nodes: var seq[TreeNode[T]], lit: var Literals) =
  mixin isAtom, fromSexp, fromSexpSym
  case n.kind
  of SList:
    assert n.len > 0
    let kind = parseEnum[T](n[0].symbol)
    if isAtom(kind):
      if n.len == 1:
        nodes.add fromSexp(kind)
      else:
        case n[1].kind
        of SInt:    nodes.add fromSexp(kind, n[1].num, lit)
        of SFloat:  nodes.add fromSexp(kind, n[1].fnum, lit)
        of SString: nodes.add fromSexp(kind, n[1].str, lit)
        else:       doAssert false
    else:
      nodes.add TreeNode[T](kind: kind, val: uint32(n.len - 1))
      for i in 1..<n.len:
        fromSexp(n[i], nodes, lit)
  of SInt:
    nodes.add fromSexp(T, n.num, lit)
  of SFloat:
    nodes.add fromSexp(T, n.fnum, lit)
  of SSymbol:
    nodes.add fromSexpSym(T, n.symbol, lit)
  else:
    doAssert false

proc fromSexp*[T](n: SexpNode): PackedTree[T] =
  ## Parses a tree from `n`, which must be the valid S-expression
  ## representation of a tree.
  var
    literals = Literals()
    nodes    = newSeq[TreeNode[T]]()
  fromSexp(n, nodes, literals)
  result = initTree(nodes, literals)
