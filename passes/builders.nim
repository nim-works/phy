## Implements an API for building a `PackedTree <builder.html#PackedTree>`_.

import
  passes/trees

type
  Builder*[T] = object
    buf: seq[TreeNode[T]]
    parent {.requiresInit.}: int
      ## the index of the current subtree node to which to add new nodes to

func initBuilder*[T](buf: sink seq[TreeNode[T]]): Builder[T] =
  ## Sets up a builder with an initial buffer (`buf`).
  Builder[T](buf: buf, parent: -1)

func initBuilder*[T](): Builder[T] =
  Builder[T](parent: -1)

template open*[T](bu: var Builder[T], k: T, body: untyped) =
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
  inc bu.buf[bu.parent].val
  bu.buf.add n

func finish*[T](bu: sink Builder[T]): seq[TreeNode[T]] =
  ## Finishes building the tree and returns the node buffer.
  result = bu.buf
