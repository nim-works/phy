## Implements the nanopass framework specific storage types for ASTs. The types
## are layered on top of `PackedTree <trees.html#PackedTree>`_.

import passes/trees

export trees.NodeIndex
# export some fundamental tree traversal and query operations, so that the
# nanopass implementation doesn't have to use bindSym everywhere
export trees.`[]`, trees.next, trees.child, trees.len
export trees.TreeNode

type
  # note: the fields are exported so that the nanopass machinery can access
  # them. User code should, in most cases, not access the fields directly
  Ast*[L: object, Storage: object] = object
    tree*: PackedTree[uint8]
      ## leaked implementation detail, don't use
    storage*: ref Storage
      ## leaked implementation detail, don't use

  Metavar*[L: object, N: static string] = object
    ## Represents a reference to an AST fragment that's a production of non-
    ## terminal `N` of language `L`.
    # TODO: rename to NonTerminal (currently clashes with the type of the same
    #       name in `nanopass.nim`)
    index*: NodeIndex
      ## leaked implementation detail, don't use

  Value*[T] = object
    ## Represents a reference to a value with type `T` that's a terminal in
    ## an AST.
    index*: uint32
      ## leaked implementation detail, don't use

  ChildSlice*[T: Metavar or Value] = object
    ## A lightweight reference to a slice of contiguous children of a tree.
    start: NodeIndex
    len: uint32

  Storage*[T] = object
    ## The container AST fragments use for storing embedded datums.
    data: seq[T] # TODO: use a BiTable

proc slice*[T](start: NodeIndex, len: uint32): ChildSlice[T] =
  ChildSlice[T](start: start, len: len)

iterator items*[T](t: PackedTree[uint8], s: ChildSlice[T]): T =
  var c = s.start
  for _ in 0..<s.len:
    yield c
    c = t.next(c)

proc `[]`*[T](t: PackedTree[uint8], s: ChildSlice[T], i: int): T =
  assert i < int(s.len)
  var n = s.start
  for _ in 0..<i:
    n = t.next(n)
  result = T(index: n)

proc high*(s: ChildSlice): int = int(s.len) - 1

# ------- Storage implementation --------

proc pack*[T](s: Storage[T], val: sink T): uint32 =
  s.data.add val
  result = s.data.high.uint32

proc unpack*[T](s: Storage[T], id: uint32): lent T =
  s.data[id]
