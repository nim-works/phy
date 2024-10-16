## Implements an API for building a `PackedTree <builder.html#PackedTree>`_.

import
  passes/trees

type
  Builder*[T] = object
    buf: seq[TreeNode[T]]
    parent {.requiresInit.}: int
      ## the index of the current subtree node to which to add new nodes to
    numPlaceholders: int
      ## number of active placeholders nodes

  Placeholder* = object
    ## Represents a placeholder node created earlier with a
    ## `Builder <#Builder>`_. It's not possible to duplicate a placeholder.

    # an object is used instead of a distinct type in order to hide the
    # implementation from external code
    pos {.requiresInit.}: int

proc `=copy`*(a: var Placeholder, b: Placeholder) {.error.}

func initBuilder*[T](buf: sink seq[TreeNode[T]]): Builder[T] =
  ## Sets up a builder with an initial buffer (`buf`).
  Builder[T](buf: buf, parent: -1)

func initBuilder*[T](): Builder[T] =
  Builder[T](parent: -1)

func initBuilder*[T](nk: T): Builder[T] =
  assert not isAtom(nk)
  Builder[T](buf: @[TreeNode[T](kind: nk)], parent: 0)

template subTree*[T](bu: var Builder[T], k: T, body: untyped) =
  ## Starts a new subtree of kind `k`.
  assert not isAtom(k)
  if bu.parent != -1:
    inc bu.buf[bu.parent].val

  if true: # open a new scope but don't interfere with break statements
    var parent = bu.buf.len
    swap(bu.parent, parent)
    bu.buf.add TreeNode[T](kind: k)
    body
    swap(bu.parent, parent)

func add*[T](bu: var Builder[T], n: TreeNode[T]) =
  ## Appends atomic node `n` to the current subtree.
  assert isAtom(n.kind)
  if bu.parent != -1:
    inc bu.buf[bu.parent].val
  bu.buf.add n

func add*[T](bu: var Builder[T], nodes: openArray[TreeNode[T]]) =
  ## Appends all `nodes` to the current sub-tree. The nodes must either
  ## represent a single atomic node, or a complete subtree.
  assert nodes.len > 0
  if bu.parent != -1:
    inc bu.buf[bu.parent].val
  bu.buf.add nodes

func copyFrom*[T](bu: var Builder[T], tree: PackedTree[T], n: NodeIndex) =
  ## Inserts the whole subtree from `tree` at `n` at the current buffer
  ## position. `tree` has to use the same underlying storage for literal
  ## data as the target tree.
  # TODO: this procedure is misguided. The builder should not handle
  #       things such as tree copies -- that's better left to ``ChangeSet``.
  if bu.parent != -1:
    inc bu.buf[bu.parent].val

  for it in tree.flat(n):
    bu.buf.add tree[it]

proc placeholder*[T](bu: var Builder[T]): Placeholder =
  ## Inserts a placeholder node into the current tree. Using the returned
  ## `Placeholder <#Placeholder>_` value, the placeholder node must later be
  ## replaced with the correct node.
  inc bu.numPlaceholders
  if bu.parent != -1:
    inc bu.buf[bu.parent].val
  bu.buf.add TreeNode[T]() # add a placeholder node
  Placeholder(pos: bu.buf.high)

proc replace*[T](bu: var Builder[T], p: sink Placeholder, n: TreeNode[T]) =
  ## Replaces the placeholder created earlier with `n`.
  assert bu.numPlaceholders > 0
  dec bu.numPlaceholders
  bu.buf[p.pos] = n

func finish*[T](bu: sink Builder[T]): seq[TreeNode[T]] =
  ## Finishes building the tree and returns the node buffer.
  assert bu.numPlaceholders == 0, "not all placeholders were replaced"
  result = bu.buf
