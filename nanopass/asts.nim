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

  ChildSlice*[T: Metavar or Value, Cursor] = object
    ## A lightweight reference to a slice of contiguous children of a tree.
    start: Cursor
    len: uint32

  Cursor* = distinct NodeIndex
    ## A cursor into a tree where without indirections.
  IndCursor* = distinct NodeIndex
    ## A cursor into a tree with indirections.

const
  RefTag* = 128'u8
    ## the node used internally for indirections

template isAtom*(x: uint8): bool =
  ## The predicate required for using an uint8 as a ``PackedTree`` tag.
  x >= RefTag

# ----- slice implementation -----

proc slice*[T, C](start: C, len: uint32): ChildSlice[T, C] =
  ChildSlice[T, C](start: start, len: len)

iterator items*[T, C](t: PackedTree[uint8], s: ChildSlice[T, C]): T =
  mixin advance
  var c = s.start
  for _ in 0..<s.len:
    when T is Metavar:
      yield T(index: get(t, c))
    else:
      yield T(index: t[pos(c)].val)
    advance(t, c)

proc `[]`*[T, C](t: PackedTree[uint8], s: ChildSlice[T, C], i: SomeInteger): T =
  mixin advance, get

  when compileOption("boundchecks"):
    when i is SomeSignedInt:
      if i < 0 or uint64(i) >= uint64(s.len):
        raise IndexDefect.newException("index out of bounds")
    else:
      if uint64(i) >= uint64(s.len):
        raise IndexDefect.newException("index out of bounds")

  var n = s.start
  for _ in 0..<i:
    advance(t, n)

  when T is Metavar:
    result = T(index: get(t, n))
  else:
    result = T(index: t[n].val)

proc len*(s: ChildSlice): int = int(s.len)
proc high*(s: ChildSlice): int = int(s.len) - 1

# ----- internal cursor API -----

# the cursor interface consists of these routines:
# * ``advance(PackedTree[uint8], var Cursor)``:
#   moves the cursor to the sibling of the current node
# * ``get(PackedTree[uint8], Cursor): NodeIndex``:
#   returns the resolved index of the node the cursor points to
# * ``pos(Cursor): NodeIndex``:
#   returns the unresolved index of the node the cursor points to
# * ``enter(PackedTree[uint8], var Cursor): Savepoint``:
#   enters the subtree at the current cursor position
# * ``restore(PackedTree[uint8], var Cursor, Savepoint)``:
#   exits the current subtree
# XXX: this should use static interfaces once supported by NimSkull

{.push stacktrace: off, inline.}

proc advance*(tree: PackedTree[uint8], cr: var Cursor) {.inline.} =
  NodeIndex(cr) = next(tree, NodeIndex(cr))

proc get*(tree: PackedTree[uint8], cr: Cursor): NodeIndex {.inline.} =
  NodeIndex cr

template pos*(cr: Cursor): NodeIndex =
  NodeIndex cr

proc enter*(tree: PackedTree[uint8], cr: var Cursor): Cursor {.inline.} =
  # nothing to step into and thus no cursor to save
  result = cr
  cr = Cursor(tree.child(NodeIndex(cr), 0))

template restore*(tree: PackedTree[uint8], cr: Cursor, saved: untyped) =
  discard # nothing to restore

# implementation for a cursor into a tree with indirections follows

proc advance*(tree: PackedTree[uint8], cr: var IndCursor) =
  NodeIndex(cr) = next(tree, NodeIndex(cr))

proc get*(tree: PackedTree[uint8], cr: IndCursor): NodeIndex =
  if tree[NodeIndex(cr)].kind == 128:
    NodeIndex tree[NodeIndex(cr)].val
  else:
    NodeIndex cr

template pos*(cr: IndCursor): NodeIndex =
  NodeIndex cr

type Savepoint = tuple[origin: IndCursor, stepped: bool]

proc enter*(tree: PackedTree[uint8], cr: var IndCursor): Savepoint =
  result = (cr, tree[NodeIndex(cr)].kind == 128)
  if result.stepped:
    cr = IndCursor tree[NodeIndex(cr)].val
  else:
    cr = IndCursor tree.child(NodeIndex(cr), 0)

template restore*(tree: PackedTree[uint8], cr: var IndCursor,
                  saved: Savepoint) =
  if saved.stepped:
    cr = saved.origin
    advance(tree, cr)
  # else: the cursor is at the correct position already

{.pop.}
