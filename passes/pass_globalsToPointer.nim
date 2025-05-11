## Turns global locations into pointer globals. Read access is turned
## into loads, write access into stores, and taking the address into copies
## of the pointer global (|L6| -> |L5|).

import
  std/[tables],
  passes/[changesets, syntax, trees]

type
  Context = object
    ptrSize: int
    globals: Table[uint32, TreeNode[NodeKind]]
      ## global ID -> global's type. Only keeps a mapping for globals that
      ## refer to addressable locations

using
  c: var Context
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var ChangeSet[NodeKind]

proc sizeAndAlignment(tree; n): tuple[size, align: uint32] =
  case tree[n].kind
  of Type:
    sizeAndAlignment(tree, tree.child(tree.child(0), tree[n].val))
  of Union, Record, Array:
    (tree[n, 0].val, tree[n, 1].val)
  of Int, UInt, Float:
    (tree[n].val, tree[n].val)
  else:
    unreachable()

proc lower(c; tree; n; bu) =
  case tree[n].kind
  of Copy:
    if tree[n, 0].kind == Global:
      # (Copy <global>) -> (Load <typ> (Copy <global>))
      c.globals.withValue tree[n, 0].val, val:
        bu.replace(n,
          bu.buildTree(
            tree(Load, node(val[]),
              tree(Copy, node(Global, tree[n, 0].val)))))
      # do nothing for simple globals
    else:
      c.lower(tree, tree.child(n, 0), bu)
  of Asgn:
    let (dst, src) = tree.pair(n)
    if tree[dst].kind == Global:
      # (Asgn <global> <src>) -> (Store <typ> (Copy <global>) <src'>)
      let src2 = bu.openTree(tree, src):
        c.lower(tree, src, bu)
      bu.replace(n, bu.buildTree(
        tree(Store, node(c.globals[tree[dst].val]),
          tree(Copy, node(tree[dst])),
          embed(src2))
      ))
    else:
      c.lower(tree, dst, bu)
      c.lower(tree, src, bu)
  of Addr:
    if tree[n, 0].kind == Global:
      # the address of the location is now stored in the global
      assert tree[n, 0].val in c.globals
      bu.replace(n, bu.buildTree(
        tree(Copy, node(tree[n, 0]))))
    else:
      c.lower(tree, tree.child(n, 0), bu)
  of Global:
    # must be a global that's used as a path element, as all other
    # possibilities are handled by the previous branches
    let id = tree[n].val
    bu.replace(n, bu.buildTree(
      tree(Deref, node(c.globals[id]),
        tree(Copy, node(Global, id)))))
  else:
    for it in tree.filter(n, {Copy, Asgn, Addr, Global}):
      c.lower(tree, it, bu)

proc lowerGlobal(c; tree; n; bu) =
  ## Turns the global loc into a simple global storing a pointer.
  let data = tree.child(n, 1)

  assert tree[data].kind == Data
  let (s, a) = sizeAndAlignment(tree, tree.child(data, 0))
  if tree.len(data) == 1:
    # (Data <typ>) -> (Data <align> <size>)
    bu.replace(n, bu.buildTree(
      tree(GlobalDef,
        node(UInt, c.ptrSize.uint32),
        tree(Data,
          # TODO: use packed values once supported, so that the full integer
          #       range works
          node(Immediate, a),
          node(Immediate, s)))))
  else:
    # (Data <typ> <content>) -> (Data <align> <content>)
    bu.replace(n, bu.buildTree(
      tree(GlobalDef,
        node(UInt, c.ptrSize.uint32),
        tree(Data,
          node(Immediate, a),
          node(tree[data, 1]))))) # the string value stays

proc lower*(tree; ptrSize: int): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of a pointer.
  var c = Context(ptrSize: ptrSize)
  let (_, globals, procs) = tree.triplet(NodeIndex(0))

  for i, it in tree.pairs(globals):
    if tree[it].kind == GlobalLoc:
      c.lowerGlobal(tree, it, result)
      c.globals[uint32 i] = tree[it, 0]

  # lower the procedure bodies:
  for it in tree.items(procs):
    if tree[it].kind == ProcDef:
      c.lower(tree, tree.child(it, 2), result)
