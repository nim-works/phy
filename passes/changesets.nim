## Implements the `ChangeSet <#ChangeSet>`_ API, which provides an efficient
## facility for modifying trees. The idea is to separate computation of what
## to modify with actually performing the modification.
##
## The new way to record changesets is via the `Cursor <#Cursor>`_ API.

import
  std/algorithm,
  passes/trees

type
  ActionKind = enum
    # **important**: the enum order informs precedence. If enum field A is
    # defined before B, A is applied first
    Insert     ## insert a new tree; source cursor doesn't change
    ChangeKind ## change the kind of a node
    ChangeLen  ## change the length of a subtree
    Skip       ## skip over the subtree at the source cursor
    SkipRaw    ## skip over N nodes
    Replace    ## Insert + Skip

  Action[T] = object
    at: NodeIndex
    case kind: ActionKind
    of ChangeKind:
      newKind: T
    of ChangeLen:
      by: uint32
    of SkipRaw:
      len: int
    of Insert, Replace:
      slice: Slice[int] ## region from the temporary buffer
    of Skip:
      discard

  ChangeSet*[T] = object
    nodes: seq[TreeNode[T]]
    actions: seq[Action[T]]

  Cursor*[T] = object
    ## A Cursor is used for tree splicing, that is, for creating a new tree
    ## by combining nodes and sub-trees from an existing `PackedTree` with
    ## new nodes and sub-trees.
    ##
    ## The Cursor itself is only used for *recording* the process -- building
    ## the resulting tree happens via `ChangeSet` application. This deferred
    ## approach allows for a limited form of nested changes. Nesting changes
    ## means modifying the content of a sub-tree *after* said sub-tree was
    ## added as a child node to another sub-tree.
    pos: NodeIndex
    len: int
      ## keeps track of the current tree's number of child nodes
    inserting: bool
      ## whether the cursor is in "insert" mode. If it is, no new ``Insert``
      ## action is needed adding new nodes
    actions: seq[Action[T]]
      ## the recorded actions
    nodes: seq[TreeNode[T]]
      ## raw node buffer

func initCursor*[T](tree: PackedTree[T]): Cursor[T] =
  ## Initializes a cursor for `tree`.
  result = Cursor[T](pos: tree.child(0))

func toChangeset*[T](cr: sink Cursor[T]): ChangeSet[T] =
  ## Creates a changeset from a cursor.
  result.nodes = move cr.nodes
  result.actions = move cr.actions

func pos*(cr: Cursor): NodeIndex {.inline.} =
  ## Returns the current cursor position.
  cr.pos

template inc(x: Cursor) =
  inc uint32(x.pos)

{.push stacktrace: off.}

proc start[T](cr: var Cursor[T]) =
  ## Enters insert mode.
  if not cr.inserting:
    cr.actions.add Action[T](at: cr.pos, kind: Insert,
                             slice: cr.nodes.len .. cr.nodes.len)
    cr.inserting = true

func stop[T](cr: var Cursor[T]) =
  ## Exits insert mode. `stop` must be called internally whenever moving the
  ## source cursor.
  if cr.inserting:
    cr.actions[^1].slice.b = cr.nodes.high # complete the action
    cr.inserting = false

{.pop.}

func keep*[T](cr: var Cursor[T], tree: PackedTree[T]) =
  ## Adds the sub-tree at current position to the current tree. Moves the
  ## cursor.
  stop(cr)
  inc cr.len
  cr.pos = tree.next(cr.pos)

func skip*[T](cr: var Cursor[T], tree: PackedTree[T]) =
  ## Skips over the node or sub-tree at the current source position, without
  ## adding it to the current tree. Moves the cursor.
  stop(cr)
  cr.actions.add Action[T](at: cr.pos, kind: Skip)
  cr.pos = tree.next(cr.pos)

func replace*[T](cr: var Cursor[T], tree: PackedTree[T], node: TreeNode[T]) =
  ## Replaces the sub-tree at the current position with `node`. Moves the
  ## cursor.
  stop(cr)
  cr.actions.add Action[T](at: cr.pos, kind: Replace,
                           slice: cr.nodes.len .. cr.nodes.len)
  cr.nodes.add node
  inc cr.len
  cr.pos = tree.next(cr.pos)

func add*[T](cr: var Cursor[T], node: TreeNode[T]) =
  ## Adds the atomic node to the sub-tree. Doesn't move the cursor.
  start(cr)
  cr.nodes.add node
  inc cr.len

template subTree*[T](cr: var Cursor[T], k: T, body: untyped) =
  ## Inserts a new sub-tree with node kind `k` at the current position. Every
  ## action within `body` appends to the tree. Doesn't move the cursor.
  if true:
    start(cr)
    let
      start = cr.nodes.len
      save = cr.len
    cr.nodes.add Node(kind: k)
    cr.len = 0
    body
    cr.nodes[start].val = cr.len.uint32
    cr.len = save + 1 # restore and add

template forEach*[T](cr: var Cursor[T], tree: PackedTree[T], name, body: untyped) =
  ## Moves the cursor through the source sub-tree, yielding to `body` for
  ## every immediate child node.
  stop(cr)
  let save = cr.len
  let len = tree.len(cr.pos)
  inc cr
  for _ in 0..<len:
    let name = cr.pos
    body
    assert cr.pos == tree.next(name), "source tree wasn't fully handled"

  cr.len = save + 1 # restore and add

template keepTree*[T](cr: var Cursor[T], tree: PackedTree[T], body: untyped) =
  ## Adds the sub-tree node at the current position to the current tree, and
  ## moves the cursor to the first child node. Makes the sub-tree the current
  ## tree.
  # XXX: maybe rename to ``modifyTree``?
  if true:
    stop(cr)
    cr.actions.add Action[T](at: cr.pos, kind: SkipRaw, len: 1)
    cr.actions.add Action[T](at: cr.pos, kind: Insert, slice: cr.nodes.len .. cr.nodes.len)
    # don't use ``start`` here, in order to prevent coalescing with following
    # insertions
    let
      save = cr.len
      start = bu.nodes.len
    cr.nodes.add tree[cr.pos]
    cr.len = 0
    inc cr
    body
    bu.nodes[start].val = cr.len.uint32
    cr.len = save + 1 # restore and add

template skipTree*[T](cr: var Cursor[T], tree: PackedTree[T], body: untyped) =
  ## Skips to the first child node of the current sub-tree. Moves the cursor.
  if true:
    stop(cr)
    cr.actions.add Action[T](at: cr.pos, kind: SkipRaw, len: 1)
    inc cr
    body

template append*[T](cr: var Cursor[T], tree: PackedTree[T], body: untyped) =
  ## Shorthand for ``keepTree`` + ``keep``. Moves the cursor.
  let len = tree.len(cr.pos)
  cr.keepTree tree:
    # keep all nodes of the sub-tree:
    for _ in len:
      cr.pos = tree.next(cr.pos)
    cr.len = len
    body

template filterTree*[T](cr: var Cursor[T], tree: PackedTree[T],
                        filter: static set[T], body: untyped) =
  ## Adds sub-tree node `n` to the current sub-tree, but with all nodes within
  ## matching `filter` modified according to `body`.
  stop(cr)
  let
    save = cr.len
    next = tree.next(cr.pos)
  inc cr
  while ord(cr.pos) < ord(next):
    if tree[cr.pos].kind in filter:
      when not defined(release):
        cr.len = 0
      body
      when not defined(release):
        # make sure the postconditions hold
        doAssert cr.len <= 1, "the child must not be expanded"
        doAssert cr.len == 1, "the child must not be removed"
      # `body` entering insert mode is fine, but we're moving the cursor
      stop(cr)
    else:
      inc cr

  cr.len = save + 1 # restore and add

func addLater*[T](cr: var Cursor[T]): int =
  ## Reserves a child slot with the current parent and returns a handle to
  ## later complete it with.
  stop(cr)
  cr.actions.add Action[T](at: cr.pos, kind: Insert)
  result = cr.actions.high
  inc cr.len

template complete*[T](cr: var Cursor[T], idx: int, k: T, body: untyped) =
  ## Records the sub-tree for a reserved slot. Doesn't affect the current
  ## cursor position or in-progress sub-tree. Within `body`, all operations
  ## moving the cursor are disallowed.
  if true:
    stop(cr)
    let
      save = cr.len
      start = cr.nodes.len
      i = idx
    cr.inserting = true # manually enter insert mode
    cr.nodes.add TreeNode[T](kind: k)
    cr.len = 0
    body
    # update the start node and action:
    cr.nodes[start].val = cr.len.uint32
    cr.actions[i].slice = start..cr.nodes.high
    # restore the previous state:
    cr.inserting = false
    cr.len = save

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
  if true:
    let
      at = n # uphold the expected evaluation order
      start = c.nodes.len

    var bu {.inject.} = initBuilder(c.nodes)
    bu.subTree(k): body
    c.nodes = finish(bu)

    c.actions.add Action[T](at: at, kind: Replace,
                            slice: start .. c.nodes.high)

func replace*[T](c: var ChangeSet[T], n: NodeIndex, with: TreeNode[T]) =
  ## Records replacing the node/subtree at `n` with `with`.
  c.actions.add Action[T](at: n, kind: Replace,
                          slice: c.nodes.len .. c.nodes.len)
  c.nodes.add with

func remove*[T](c: var ChangeSet[T], tree: PackedTree[T], n: NodeIndex, i: int) =
  ## Records the removal of the `i`-th node from `n`.
  c.actions.add Action[T](at: n, kind: ChangeLen, by: 0xFFFF_FFFF'u32) # -1
  c.actions.add Action[T](at: tree.child(n, i), kind: Skip)

func insert*[T](c: var ChangeSet[T], tree: PackedTree[T], n: NodeIndex,
                i: int, node: TreeNode[T]) =
  ## Records the insertion of `node` at the `i`-th child node of `n`.
  c.actions.add Action[T](at: n, kind: ChangeLen, by: 1)
  c.actions.add Action[T](at: tree.child(n, i), kind: Insert,
                          slice: c.nodes.len .. c.nodes.len)
  c.nodes.add node

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
  # sort the actions by source position and action:
  sort(c.actions, proc(a, b: auto): int =
    result = a.at.int - b.at.int
    if result == 0:
      result = ord(a.kind) - ord(b.kind)
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
    of SkipRaw:
      inc source, it.len
    of Insert:
      nodes.add c.nodes.toOpenArray(it.slice.a, it.slice.b)
    of Replace:
      source = tree.next(it.at).int
      nodes.add c.nodes.toOpenArray(it.slice.a, it.slice.b)

  # copy the remaining nodes, if any:
  if source < tree.nodes.len:
    nodes.add toOpenArray(tree.nodes, source, tree.nodes.high)

  result = initTree(nodes, tree.literals)
