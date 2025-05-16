## Simple stack allocation pass. Adds a frame pointer local to all procedures
## that use stack memory and turns blob locals into stack locations
## (|L2| -> |L1|).

import
  passes/[changesets, syntax, trees]

type
  Node = TreeNode[NodeKind]

  Context = object
    # per-procedure state:
    locals: seq[tuple[onStack: bool, offset: uint32]]
      ## for stack locations, `offset` is the byte offset of the location.
      ## For non-stack-locations, it's the register/local ID
    framePointer: Node
      ## the local storing the frame pointer

using
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var ChangeSet[NodeKind]

func id(n: Node): uint32 =
  assert n.kind == Local
  n.val

func isBlob(tree; n): bool =
  case tree[n].kind
  of Blob: true
  of Type: tree[tree.child(0), tree[n].val].kind == Blob
  of Int, UInt, Float, Ptr: false
  else:    unreachable()

func sizeAndAlign(tree, n): (uint32, uint32) =
  var n = n
  # resolve the indirection:
  if tree[n].kind == Type:
    n = tree.child(tree.child(0), tree[n].val)

  result = (tree[n, 0].val, tree[n, 1].val)

proc lowerInExpr(c: Context; tree; n; bu) =
  case tree[n].kind
  of Local:
    let local = tree[n].id
    assert not c.locals[local].onStack
    if local != c.locals[local].offset:
      # reduce changeset size by only replacing the node when the ID changes
      bu.replace n, Node(kind: Local, val: c.locals[local].offset)
  of Addr:
    let local = tree[n, 0].id
    assert c.locals[local].onStack

    if c.locals[local].offset == 0:
      # no addition is necessary
      bu.replace n:
        bu.buildTree tree(Copy, node(c.framePointer))
    else:
      # XXX: it could make sense to try merging the offset computation into
      #      an enclosing one, where possible
      bu.replace n:
        bu.buildTree:
          tree(Offset,
            tree(Copy, node(c.framePointer)),
            node(IntVal, c.locals[local].offset),
            node(IntVal, 1))

  else:
    for it in tree.filter(n, {Local, Addr}):
      c.lowerInExpr(tree, it, bu)

proc lowerProc(c: var Context; tree; n; bu) =
  let (_, localsNode, blocks) = tree.triplet(n)
  c.locals.setLen(tree.len(localsNode))

  var
    nextId = 0'u32
    stackOffset = 0'u32

  # assign a stack location to every blob local. At the moment, blob locals
  # are put into consecutive stack location, regardless of whether they have
  # disjoint lifetimes or not
  for i, it in tree.pairs(localsNode):
    if isBlob(tree, it):
      let (size, align) = sizeAndAlign(tree, it)
      doAssert align <= 8, "over-aligned locals are currently not supported"
      # align the stack offset:
      stackOffset = (stackOffset + (align - 1)) and not (align - 1)
      c.locals[i] = (true, stackOffset)
      stackOffset += size # reserve the needed space
    else:
      c.locals[i] = (false, nextId)
      inc nextId

  # make the frame size a multiple of 8, so that the start of stack frame is
  # always on an 8 byte boundary
  stackOffset = (stackOffset + 7) and not 7'u32

  if stackOffset == 0:
    # the body stays as is, only the header needs to be modified
    bu.modifyTree tree, n, m:
      bu.insert m, localsNode, Node(kind: Immediate, val: stackOffset)
      discard
    return

  c.framePointer = Node(kind: Local, val: nextId)

  bu.modifyTree tree, n, m:
    bu.insert m, localsNode, Node(kind: Immediate, val: stackOffset)
    bu.modifyTree tree, localsNode, t:
      # remove all stack locals from the list of locals:
      for i, it in tree.pairs(localsNode):
        if c.locals[i].onStack:
          bu.remove(t, it)

      # add the frame-pointer local to the list of locals:
      bu.insert t, tree.fin(localsNode), Node(kind: Ptr)

    for i, blk in tree.pairs(blocks):
      let params = tree.child(blk, 0)
      if tree.len(params) > 0 or i == 0:
        bu.modifyTree tree, params, m:
          # patch the IDs in the block parameter list:
          for it in tree.items(params):
            bu.replace it, Node(kind: Local, val: c.locals[tree[it].id].offset)

          if i == 0:
            # the entry block provides the local to store the frame pointer in
            bu.insert m, tree.fin(params), c.framePointer

      for s in tree.items(blk, 1): # go over all statements
        c.lowerInExpr(tree, s, bu)

proc lower*(tree): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = Context()

  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      c.lowerProc(tree, it, result)
