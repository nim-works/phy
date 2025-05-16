## Turns all non-blob locals that have their address taken into blob locals.
## Goes from |L3| code to |L2| code.

import
  std/[packedsets],
  passes/[changesets, syntax, trees]

type
  LocalId = distinct uint32

  Context = object
    ptrSize: int
    # per-procedure context:
    locals: NodeIndex
    marker: PackedSet[LocalId]

  Node = TreeNode[NodeKind]

using
  c: var Context
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var ChangeSet[NodeKind]

func local(n: Node): LocalId =
  assert n.kind == Local
  LocalId(n.val)

proc resolve(tree; n: NodeIndex): NodeIndex =
  case tree[n].kind
  of Type: tree.child(tree.child(0), tree[n].val)
  else:    n

proc typeof(c; tree; id: LocalId): NodeIndex =
  tree.child(c.locals, ord id)

proc sizeAndAlignment(c; tree; n): (uint32, uint32) =
  case tree[n].kind
  of Int, UInt, Float:
    (tree[n].val, tree[n].val)
  of Ptr:
    (c.ptrSize.uint32, c.ptrSize.uint32)
  else:
    unreachable()

proc isSimple(tree; n): bool =
  case tree[n].kind
  of Int, UInt, Float, Ptr: true
  of Blob: false
  of Type: isSimple(tree, tree.child(tree.child(0), tree[n].val))
  else:    unreachable()

proc lowerExpr(c; tree; n; bu) =
  for it in tree.filter(n, {Copy}):
    if tree[it, 0].kind == Local and tree[it, 0].local in c.marker:
      # (Copy local) -> (Load typ (Addr local))
      bu.replace it:
        bu.buildTree:
          tree(Load,
            embed(c.typeof(tree, tree[it, 0].local)),
            tree(Addr, embed(tree.child(it, 0))))

proc lowerStmt(c; tree; n; bu) =
  case tree[n].kind
  of Asgn:
    let (a, b) = tree.pair(n)
    if tree[a].local in c.marker:
      # (Asgn a b) -> (Store typ (Addr a) b')
      let b2 = bu.openTree(tree, b): c.lowerExpr(tree, b, bu)
      bu.replace n:
        bu.buildTree:
          tree(Store,
            embed(c.typeof(tree, tree[a].local)),
            tree(Addr, embed(a)),
            embed(b2))
    else:
      c.lowerExpr(tree, b, bu)
  else:
    c.lowerExpr(tree, n, bu)

proc lowerProc(c; tree; n; bu) =
  c.marker.clear()
  c.locals = tree.child(n, 1)
  let body = tree.child(n, 2)

  # first pass: look for locals of primitive type that have their address
  # taken
  for it in tree.filter(body, {Addr}):
    if tree.isSimple(c.typeof(tree, tree[it, 0].local)):
      c.marker.incl tree[it, 0].local

  if c.marker.len() == 0:
    return # nothing to do

  var newLocals: seq[Node]

  for i, blk in tree.pairs(body):
    # if a block parameter (which can only be of primitive type at this
    # point) has its address taken, the parameter must be turned back into a
    # primitive type. In effect, this means that the real parameter is copied
    # to a stack location on block entry that the rest of the procedure
    # then uses in place of the real parameter
    bu.modifyTree tree, blk, m:
      for it in tree.items(tree.child(blk, 0)):
        let id = tree[it].local
        if id in c.marker:
          let newId = tree.len(c.locals) + newLocals.len
          # replace the parameter with a fresh local:
          newLocals.add tree[c.locals, ord id]
          bu.replace it, Node(kind: Local, val: uint32 newId)
          # insert the copy at the start of the block:
          bu.insert m, tree.child(blk, 1):
            bu.buildTree:
              tree(Store, node(newLocals[^1]),
                tree(Addr, node(Local, uint32 id)),
                tree(Copy, node(Local, uint32 newId)))

      for it in tree.items(blk, 1):
        c.lowerStmt(tree, it, bu)

  bu.modifyTree tree, c.locals, m:
    for it in c.marker.items:
      let
        slot = tree.child(c.locals, ord it)
        (size, align) = sizeAndAlignment(c, tree, tree.resolve(slot))
      bu.replace slot:
        bu.buildTree tree(Blob, node(Immediate, size), node(Immediate, align))

    for it in newLocals.items:
      bu.insert m, tree.fin(c.locals), it

proc lower*(tree; ptrSize: Positive): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).

  var c = Context(ptrSize: ptrSize)
  # lower the procedures:
  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      c.lowerProc(tree, it, result)
