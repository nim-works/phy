## Implements the ``PackedTree`` storage type, for space efficient storage of
## arbitrary trees. A packed tree is just a sequence of nodes, with each node
## either being a leaf or subtree node.

import
  std/strutils

type
  PackedTree*[T] = object
    ## Stores a node tree packed together in a single sequence.
    nodes*: seq[T]

  NodeIndex* = distinct uint32

func `==`*(a, b: NodeIndex): bool {.borrow.}

proc initTree*[T](nodes: sink seq[T]): PackedTree[T] =
  PackedTree[T](nodes: nodes)

proc `[]`*[T](t: PackedTree[T], at: NodeIndex): T {.inline.} =
  t.nodes[ord at]

proc contains*(t: PackedTree, n: NodeIndex): bool {.inline.} =
  ## Returns whether `n`, the node index, exists within `t`, the tree.
  ord(n) in 0..<t.nodes.len

proc next*(t: PackedTree, i: NodeIndex): NodeIndex =
  ## Returns the index of the first node following `i` that is not a child
  ## node of `i`.
  mixin isAtom
  var
    i = uint32(i)
    last = i
  while i <= last:
    if not isAtom(t.nodes[i].kind):
      last += t.nodes[i].val
    inc i

  result = NodeIndex(i)

func first*(t: PackedTree, n: NodeIndex): NodeIndex {.inline.} =
  ## Returns the index of the first sub-node of `n`.
  NodeIndex(uint32(n) + 1)

proc child*(t: PackedTree, i: NodeIndex, child: Natural): NodeIndex =
  ## Returns the index of the `child`-th subnode of `i`.
  result = t.first(i)
  for _ in 0..<child:
    result = t.next(result)

proc child*(t: PackedTree, i: NodeIndex, child: BackwardsIndex
           ): NodeIndex {.inline.} =
  ## Returns the index of the `child`-th (backwards) subnode of `i`.
  t.child(i, t[i].val.int - ord(child))

proc child*(t: PackedTree, i: Natural): NodeIndex =
  ## Returns the index of the `i`th subnode of the top-level node.
  child(t, NodeIndex(0), i)

proc `[]`*[T](t: PackedTree[T], i: NodeIndex, child: Natural): T {.inline.} =
  t.nodes[ord t.child(i, child)]

proc len*(t: PackedTree, i: NodeIndex): int =
  t.nodes[ord i].val.int

proc last*(tree: PackedTree, n: NodeIndex): NodeIndex =
  tree.child(n, tree.len(n) - 1)

proc fin*(tree: PackedTree, n: NodeIndex): NodeIndex =
  ## Returns the node one past the last node part of the subtree at `n`.
  tree.next(n)

iterator items*(t: PackedTree, at: NodeIndex): NodeIndex =
  ## Returns the index of each child node of the node at `at`.
  var n = t.first(at)
  for i in 0..<t.len(at):
    yield n
    n = t.next(n)

iterator items*(t: PackedTree, at: NodeIndex; start: int; last = ^1): NodeIndex =
  ## Returns the index of each child node of the node at `at`, only
  ## including subnode in slice ``start..last``.
  var n = t.first(at)
  var i = 0
  while i < start:
    n = t.next(n)
    inc i

  let last = t.len(at) - ord(last)
  while i <= last:
    yield n
    n = t.next(n)
    inc i

iterator pairs*(t: PackedTree, at: NodeIndex): (int, NodeIndex) =
  ## Returns the child number + child node index for all child nodes of `at`.
  var n = t.first(at)
  for i in 0..<t.len(at):
    yield (i, n)
    n = t.next(n)

iterator flat*(t: PackedTree, at: NodeIndex): NodeIndex =
  ## Returns all nodes spanned by the tree node at `at`, including `at`
  ## itself.
  mixin isAtom
  var
    i = uint32(at)
    last = i
  while i <= last:
    yield NodeIndex(i)
    if not isAtom(t.nodes[i].kind):
      last += t.nodes[i].val
    inc i

iterator filter*[T, U](t: PackedTree[T], at: NodeIndex,
                       filter: static set[U]): NodeIndex =
  ## Returns all nodes matching `filter` in the tree at `at`. The returned
  ## nodes/trees are *not* recursed into.
  # a static set is used for the sake of run-time efficiency; the sets can
  # become quite large
  # XXX: this iterator should move to a separate module focused on a tree
  #      pattern matching API
  mixin isAtom
  var
    i = uint32(at)
    last = i
  while i <= last:
    let n = t.nodes[i]
    if n.kind in filter:
      yield NodeIndex(i)
      let ne = t.next(NodeIndex i).uint32
      last += ne - i - 1
      i = ne
    else:
      if not isAtom(n.kind):
        last += n.val
      inc i

func pair*(tree: PackedTree, n: NodeIndex): (NodeIndex, NodeIndex) =
  ## Returns the index of the first and second subnode of `n`.
  result[0] = tree.child(n, 0)
  result[1] = tree.next(result[0])

func triplet*(tree: PackedTree, n: NodeIndex): (NodeIndex, NodeIndex, NodeIndex) =
  ## Returns the index of the first, second, and third subnode of `n`.
  result[0] = tree.child(n, 0)
  result[1] = tree.next(result[0])
  result[2] = tree.next(result[1])
