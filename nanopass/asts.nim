## Implements the nanopass framework specific storage types for ASTs. The types
## are layered on top of `PackedTree <trees.html#PackedTree>`_.

import passes/trees

export trees.NodeIndex
# export some fundamental tree traversal and query operations, so that the
# nanopass implementation doesn't have to use bindSym everywhere
export trees.`[]`, trees.next, trees.child, trees.len
export trees.TreeNode

type
  Tag* = uint8
  AstNode* = TreeNode[Tag]
  Tree* = PackedTree[Tag]

  # note: the fields are exported so that the nanopass machinery can access
  # them. User code should, in most cases, not access the fields directly
  Ast*[L: object, Storage: object] = object
    tree*: Tree
      ## leaked implementation detail, don't use
    storage*: ref Storage
      ## leaked implementation detail, don't use
    records*: typeof(L.meta.records)
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

  RecordRef*[L: object, N: static string] = object
    ## A reference to a record of a language.
    id*: uint32
      ## leaked implementation detail, don't use

  ChildSlice*[T: Metavar or RecordRef or Value, Cursor] = object
    ## A lightweight reference to a sequence of sibling nodes. The reference
    ## must not outlive the spawned-from tree.
    tree: ptr Tree
    start: Cursor
    len: uint32

  Cursor* = distinct NodeIndex
    ## A cursor into a tree where without indirections.
  IndCursor* = distinct NodeIndex
    ## A cursor into a tree with indirections.

const
  RefTag* = 128'u8
    ## the node used internally for indirections

template tag*(n: AstNode): uint8 =
  ## The node's tag.
  n.kind

template isAtom*(x: Tag): bool =
  ## The predicate required for using an uint8 as a ``PackedTree`` tag.
  x >= RefTag

{.push stacktrace: off, profiler: off.}

proc `tag=`*(n: var AstNode, tag: uint8) {.inline.} =
  ## Sets the tag of `n` to `tag`. A low-level operation.
  n.kind = tag

proc `==`(a, b: AstNode): bool {.inline.} =
  ## Compares the nodes for equality, ignoring source location info.
  a.tag == b.tag and a.val == b.val

{.pop.}

template node*(tag: uint8, v: uint32): AstNode =
  AstNode(kind: tag, val: v)

# ----- slice implementation -----

proc slice*[T, C](tree: ptr Tree, start: C, len: uint32): ChildSlice[T, C] =
  ## Creates a reference to `len` sibling nodes starting at `start`.
  ChildSlice[T, C](tree: tree, start: start, len: len)

template load[T, C](tree: Tree, c: C): T =
  mixin get, pos
  when T is Metavar:   T(index: get(tree, c))
  elif T is RecordRef: T(id: tree[pos(c)].val)
  else:                T(index: tree[pos(c)].val)

iterator items*[T, C](s: ChildSlice[T, C]): T =
  mixin advance
  var c = s.start
  for _ in 0..<s.len:
    yield load[T](s.tree[], c)
    advance(s.tree[], c)

iterator pairs*[T, C](s: ChildSlice[T, C]): (int, T) =
  mixin advance
  var c = s.start
  for i in 0..<s.len:
    yield (int(i), load[T](s.tree[], c))
    advance(s.tree[], c)

proc `[]`*[T, C](s: ChildSlice[T, C], i: SomeInteger): T =
  mixin advance

  when compileOption("boundchecks"):
    when i is SomeSignedInt:
      if i < 0 or uint64(i) >= uint64(s.len):
        raise IndexDefect.newException("index out of bounds")
    else:
      if uint64(i) >= uint64(s.len):
        raise IndexDefect.newException("index out of bounds")

  var n = s.start
  for _ in 0..<i:
    advance(s.tree[], n)

  result = load[T](s.tree[], n)

proc len*(s: ChildSlice): int = int(s.len)
proc high*(s: ChildSlice): int = int(s.len) - 1

# ----- internal cursor API -----

# the cursor interface consists of these routines:
# * ``advance(Tree, var Cursor)``:
#   moves the cursor to the sibling of the current node
# * ``get(Tree, Cursor): NodeIndex``:
#   returns the resolved index of the node the cursor points to
# * ``pos(Cursor): NodeIndex``:
#   returns the unresolved index of the node the cursor points to
# * ``enter(Tree, var Cursor): Savepoint``:
#   enters the subtree at the current cursor position
# * ``restore(Tree, var Cursor, Savepoint)``:
#   exits the current subtree
# XXX: this should use static interfaces once supported by NimSkull

{.push stacktrace: off, inline.}

proc advance*(tree: Tree, cr: var Cursor) {.inline.} =
  NodeIndex(cr) = next(tree, NodeIndex(cr))

proc get*(tree: Tree, cr: Cursor): NodeIndex {.inline.} =
  NodeIndex cr

template pos*(cr: Cursor): NodeIndex =
  NodeIndex cr

proc enter*(tree: Tree, cr: var Cursor): Cursor {.inline.} =
  # nothing to step into and thus no cursor to save
  result = cr
  cr = Cursor(tree.child(NodeIndex(cr), 0))

template restore*(tree: Tree, cr: Cursor, saved: untyped) =
  discard # nothing to restore

# implementation for a cursor into a tree with indirections follows

proc advance*(tree: Tree, cr: var IndCursor) =
  NodeIndex(cr) = next(tree, NodeIndex(cr))

proc get*(tree: Tree, cr: IndCursor): NodeIndex =
  if tree[NodeIndex(cr)].tag == 128:
    NodeIndex tree[NodeIndex(cr)].val
  else:
    NodeIndex cr

template pos*(cr: IndCursor): NodeIndex =
  NodeIndex cr

type Savepoint = tuple[origin: IndCursor, stepped: bool]

proc enter*(tree: Tree, cr: var IndCursor): Savepoint =
  result = (cr, tree[NodeIndex(cr)].tag == 128)
  if result.stepped:
    cr = IndCursor tree[NodeIndex(cr)].val
  else:
    cr = IndCursor tree.child(NodeIndex(cr), 0)

template restore*(tree: Tree, cr: var IndCursor,
                  saved: Savepoint) =
  if saved.stepped:
    cr = saved.origin
    advance(tree, cr)
  # else: the cursor is at the correct position already

{.pop.}

# ------ additional tree operations --------

proc equal*(tree: Tree, a, b: Cursor): bool =
  ## Compares the nodes/sub-trees at `a` and `b` for structural equality.
  if pos(a) == pos(b):
    return true

  var (a, b) = (a, b)
  var i = 1'u32
  while i > 0:
    let n = tree[pos(a)]
    if n != tree[pos(b)]:
      return false
    elif not isAtom(n.kind):
      i += n.val
    advance(tree, a)
    advance(tree, b)
    dec i

  result = true

proc equal*(tree: Tree, a, b: IndCursor): bool =
  ## Compares the nodes/sub-trees at `a` and `b` for structural equality.
  if pos(a) == pos(b):
    return true

  # needs a stack for bookkeeping
  var (a, b) = (a, b)
  var stack: seq[(IndCursor, IndCursor, uint32)]
  var i = 1'u32
  while true:
    let na = tree[pos(a)]
    let nb = tree[pos(b)]
    if na != nb:
      if na.tag == RefTag:
        stack.add (a, b, i)
        i = 1
        a = IndCursor(na.val)
        continue
      elif nb.tag == RefTag:
        stack.add (a, b, i)
        i = 1
        b = IndCursor(nb.val)
        continue
      return false
    elif na.tag == RefTag:
      stack.add (a, b, i)
      i = 1
      a = IndCursor(na.val)
      b = IndCursor(nb.val)
      continue
    elif not isAtom(na.kind):
      i += na.val
    dec i
    if i == 0:
      if stack.len == 0:
        break
      (a, b, i) = stack.pop()
    else:
      advance(tree, a)
      advance(tree, b)

  result = true
