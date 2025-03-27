## Provides the implementation for the built-in meta-language functions, to
## be used by the interpreter.

import std/tables
import bignums, rationals
import types except Node

type Node = types.Node[TypeId]

proc `==`*(a, b: Node): bool =
  if a.kind == b.kind:
    case a.kind
    of withChildren:
      a.children == b.children
    of nkHole, nkFail, nkFalse, nkTrue:
      true
    of nkNumber:
      a.num == b.num
    of nkSymbol, nkString:
      a.sym == b.sym
    of nkFunc, nkRelation, nkContext, nkVar:
      a.id == b.id
    of nkType:
      a.typ == b.typ
  else:
    false

proc makeNum(r: Rational): Node =
  Node(kind: nkNumber, num: r)

proc merge(a: var Node, b: Node) =
  ## Merges the record/set/map `b` into `a`.
  case b.kind
  of nkMap:
    for it in b.children.items:
      block merge:
        for x in a.children.mitems:
          if x[0] == it[0]:
            x[1].merge(it[1])
            break merge
        a.add it
  of nkSet:
    for it in b.children.items:
      block merge:
        for x in a.children.items:
          if x == it:
            break merge
        a.add it
  of nkRecord:
    for it in b.children.items:
      block merge:
        for x in a.children.mitems:
          if x[0].sym == it[0].sym:
            x[1].merge(it[1])
            break merge
        a.add it
  else:
    a = b

proc contains(n, elem: Node): bool =
  for it in n.children.items:
    if it.kind == nkAssoc:
      if it[0] == elem:
        return true
    elif it == elem:
      return true
  result = false

proc toNode(val: bool): Node =
  if val: Node(kind: nkTrue)
  else:   Node(kind: nkFalse)

const arr = [
  ("same",  proc(n: Node): Node = toNode n[0] == n[1]),
  ("in",    proc(n: Node): Node = toNode contains(n[1], n[0])),
  ("notin", proc(n: Node): Node = toNode not(contains(n[1], n[0]))),
  ("+", proc(n: Node): Node =
    case n[0].kind
    of nkNumber:
      result = makeNum(n[0].num + n[1].num)
    of nkRecord, nkMap, nkSet:
      # merge the right record into the left one
      result = n[0]
      result.merge(n[1])
    else:
      doAssert false
  ),
  ("-", proc(n: Node): Node = makeNum(n[0].num - n[1].num)),
  ("*", proc(n: Node): Node = makeNum(n[0].num * n[1].num)),
  ("/", proc(n: Node): Node = makeNum(n[0].num / n[1].num)),
  ("neg", proc(n: Node): Node = makeNum(-n.num)),
  ("^", proc(n: Node): Node =
    let base = n[0].num
    let exponent = n[1].num.toInt
    if exponent == 0'n:
      Node(kind: nkNumber, num: rational(1))
    elif exponent.isNeg:
      var val = base
      for _ in 1'n..<abs(exponent):
        val = val * base
      makeNum(reciprocal(val))
    else:
      var val = base
      for _ in 1'n..<exponent:
        val = val * base
      makeNum(val)
  ),
  ("<", proc(n: Node): Node = toNode n[0].num < n[1].num),
  ("<=", proc(n: Node): Node = toNode n[0].num <= n[1].num),
  ("len", proc(n: Node): Node = Node(kind: nkNumber, num: rational(n.len))),
  ("map", proc(n: Node): Node =
    # create a map from the list of key/value pairs
    result = Node(kind: nkMap)
    for it in n.children.items:
      result.add tree(nkAssoc, it[0], it[1])
  ),
  ("zip", proc(n: Node): Node =
    # create a single list from the two lists of tuples
    result = Node(kind: nkGroup)
    assert n.kind == nkTuple
    assert n.len == 2
    assert n[0].kind == nkGroup
    assert n[1].kind == nkGroup
    for i in 0..<min(n[0].len, n[1].len):
      result.add tree(nkTuple, n[0][i], n[1][i])
  ),
  ("updated", proc(n: Node): Node =
    let idx = toInt(n[1].num)
    assert n[0].kind == nkGroup
    assert idx in 0..n[0].children.high
    result = n[0]
    result.children[idx] = n[2]
  )]

const functions* = block:
  # XXX: for unknown reasons, ``toTable`` cannot be used here, as it crashes
  #      the VM...
  var tab: Table[string, proc(n: Node): Node {.nimcall.}]
  for (name, prc) in arr.items:
    tab[name] = prc
  tab
