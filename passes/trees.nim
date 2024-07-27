## Implements the ``PackedTree`` storage type, for space efficient storage of
## arbitrary trees.

import
  std/strutils,
  experimental/sexp

type
  TreeNode*[T] = object
    ## A single node. How the val field is interpreted depends on the kind. For
    ## leaf nodes, the field's meaning is decided externally, while for non-
    ## leaf nodes, `val` stores how many child nodes the node has.
    kind*: T
    val*: uint32

  PackedTree*[T] = object
    ## Stores a node tree packed together in a single sequence.
    nodes: seq[TreeNode[T]]
    numbers: seq[uint64]
    # TODO: use a BiTable for the numbers

  NodeIndex* = distinct uint32

const
  ExternalFlag = 0x8000_0000'u32
    ## use the most significant bit to flag whether the value is larger than an
    ## `max(int32)` and overflows into `PackedTree.numbers`.

proc `[]`*[T](t: PackedTree[T], at: NodeIndex): TreeNode[T] {.inline.} =
  t.nodes[ord at]

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

proc `[]`*[T](t: PackedTree[T], i: NodeIndex, child: Natural
             ): TreeNode[T] {.inline.} =
  t.nodes[ord t.child(i, child)]

proc len*(t: PackedTree, i: NodeIndex): int =
  t.nodes[ord i].val.int

proc last*(tree: PackedTree, n: NodeIndex): NodeIndex =
  tree.child(n, tree.len(n) - 1)

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

func pair*(tree: PackedTree, n: NodeIndex): (NodeIndex, NodeIndex) =
  ## Returns the index of the first and second subnode of `n`.
  result[0] = tree.child(n, 0)
  result[1] = tree.next(result[0])

func triplet*(tree: PackedTree, n: NodeIndex): (NodeIndex, NodeIndex, NodeIndex) =
  ## Returns the index of the first, second, and third subnode of `n`.
  result[0] = tree.child(n, 0)
  result[1] = tree.next(result[0])
  result[2] = tree.next(result[1])

proc getInt*(tree: PackedTree, n: NodeIndex): int64 =
  ## Returns the number stored by `n` as a signed integer.
  let val = tree[n].val
  if (val and ExternalFlag) != 0:
    cast[int64](tree.numbers[val and not(ExternalFlag)])
  else:
    int64(val)

proc getUInt*(tree: PackedTree, n: NodeIndex): uint64 =
  ## Returns the number stored by `n` as an unsigned integer.
  let val = tree[n].val
  if (val and ExternalFlag) != 0:
    tree.numbers[val or not(ExternalFlag)]
  else:
    val

proc getFloat*(tree: PackedTree, n: NodeIndex): float64 =
  ## Returns the number stored by `n` as a float.
  cast[float64](tree.numbers[tree[n].val])

proc pack*(tree: var PackedTree, i: int64): uint32 =
  ## Packs `i` into an ``uint32`` value that can be stored in a ``TreeNode``.
  if i >= 0 and i < int64(ExternalFlag):
    result = uint32(i) # fits into a uint32
  else:
    result = tree.numbers.len.uint32 or ExternalFlag
    tree.numbers.add(cast[uint64](i))

proc pack*(tree: var PackedTree, f: float64): uint32 =
  ## Packs `f` into an ``uint32`` value that can be stored in a ``TreeNode``.
  result = tree.numbers.len.uint32
  tree.numbers.add(cast[uint64](f))

# TODO: move the S-expression serialization/deserialization elsewhere

proc toSexp*[T](tree: PackedTree[T], at: NodeIndex): SexpNode =
  mixin isAtom, toSexp
  if isAtom(tree[at].kind):
    result = toSexp(tree[at])
  else:
    result = newSList()
    result.add newSSymbol($tree[at].kind)
    for it in tree.items(at):
      result.add toSexp(tree, it)

proc fromSexp[T](n: SexpNode, to: var PackedTree[T]) =
  mixin isAtom, fromSexp
  case n.kind
  of SList:
    assert n.len > 0
    let kind = parseEnum[T](n[0].symbol)
    if isAtom(kind):
      to.nodes.add fromSexp(to, kind, n)
    else:
      to.nodes.add TreeNode[T](kind: kind, val: uint32(n.len - 1))
      for i in 1..<n.len:
        fromSexp(n[i], to)
  of SInt:
    to.nodes.add fromSexp(n.num)
  else:
    doAssert false

proc fromSexp*[T](n: SexpNode): PackedTree[T] =
  fromSexp(n, result)