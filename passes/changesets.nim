## Implements the `ChangeSet <#ChangeSet>`_ API, which provides an efficient
## facility for modifying trees. The idea is to separate computation of what
## to modify with actually performing the modification.

import
  std/algorithm,
  passes/trees

type
  ActionKind = enum
    ChangeKind ## change the kind of a node
    ChangeLen  ## change the length of a subtree
    Skip       ## skip over the subtree at the source cursor
    Insert     ## insert a new tree; source cursor doesn't change
    Replace    ## Insert + Skip

  Action[T] = object
    at: NodeIndex
    case kind: ActionKind
    of ChangeKind:
      newKind: T
    of ChangeLen:
      by: uint32
    of Insert, Replace:
      slice: Slice[int] ## region from the temporary buffer
    of Skip:
      discard

  ChangeSet*[T] = object
    nodes: seq[TreeNode[T]]
    actions: seq[Action[T]]

func changeKind*[T](c: var ChangeSet[T], n: NodeIndex, kind: T) =
  ## Records changing the kind of node `n` to `kind`.
  c.actions.add Action[T](at: n, kind: ChangeKind, newKind: kind)

template replace*[T](c: var ChangeSet[T], n: NodeIndex, body: untyped) =
  ## Records replacing the node/sub-tree at `n` with a node/sub-tree created
  ## by `body`. For this, a builder instance named ``bu`` is available to the
  ## body.
  if true:
    let
      at = n # uphold the expected evaluation order
      start = c.nodes.len

    var bu {.inject.} = initBuilder(c.nodes)
    body
    c.nodes = finish(bu)

    c.actions.add Action[T](at: at, kind: Replace,
                            slice: start .. c.nodes.high)

template replace*[T](c: var ChangeSet[T], n: NodeIndex, k: T,
                     body: untyped) =
  ## Records replacing the node/subtree at `n` with a new tree of kind `k`. The
  ## new tree is built by `body`, with a builder named ``bu`` injected into the
  ## scope.
  replace(c, n):
    bu.subTree(k): body

func replace*[T](c: var ChangeSet[T], n: NodeIndex, with: TreeNode[T]) =
  ## Records replacing the node/subtree at `n` with `with`.
  c.actions.add Action[T](at: n, kind: Replace,
                          slice: c.nodes.len .. c.nodes.len)
  c.nodes.add with

func remove*[T](c: var ChangeSet[T], tree: PackedTree[T], n: NodeIndex, i: int) =
  ## Records the removal of the `i`-th node from `n`.
  c.actions.add Action[T](at: n, kind: ChangeLen, by: 0xFFFF_FFFF'u32) # -1
  c.actions.add Action[T](at: tree.child(n, i), kind: Skip)

template insert*[T](c: var ChangeSet[T], tree: PackedTree[T], n: NodeIndex,
                    i: int, k: T, body: untyped) =
  ## Records the insertion of a new subtree at the `i`-th child node of `n`.
  ## A builder named `bu` is injected into the scope `body` is evaluated
  ## within.
  if true:
    let
      at = n
      idx = i
      start = c.nodes.len
    var bu {.inject.} = initBuilder(c.nodes)
    bu.subTree(k): body
    c.nodes = finish(bu)

    c.actions.add Action[T](at: at, kind: ChangeLen, by: 1)
    c.actions.add Action[T](at: tree.child(at, idx), kind: Insert,
                            slice: start .. c.nodes.high)

func apply*[T](tree: PackedTree[T], c: sink ChangeSet[T]): PackedTree[T] =
  ## Applies the changeset `c` to `tree`.
  # sort the actions by source position:
  sort(c.actions, proc(a, b: auto): int =
    a.at.int - b.at.int
  )

  var
    nodes: seq[TreeNode[T]]
    source = 0 ## cursor into the source node sequence

  for it in c.actions.items:
    if it.at.int > source:
      nodes.add toOpenArray(tree.nodes, source, it.at.int - 1)
      source = it.at.int # move to the action position

    case it.kind
    of ChangeKind:
      var n = tree[it.at]
      n.kind = it.newKind
      nodes.add n
      inc source
    of ChangeLen:
      # multiple "change length" actions per node are supported; only copy
      # the target node once
      if source <= it.at.int:
        nodes.add tree[it.at]
        inc source

      nodes[^1].val += it.by
    of Skip:
      source = tree.next(it.at).int
    of Insert:
      nodes.add c.nodes.toOpenArray(it.slice.a, it.slice.b)
    of Replace:
      source = tree.next(it.at).int
      nodes.add c.nodes.toOpenArray(it.slice.a, it.slice.b)

  # copy the remaining nodes, if any:
  if source < tree.nodes.len:
    nodes.add toOpenArray(tree.nodes, source, tree.nodes.high)

  result = initTree(nodes, tree.literals)
