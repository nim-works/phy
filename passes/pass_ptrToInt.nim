## Turns pointer types into unsigned integers (|LPtr| -> |L0|).

import
  passes/[changesets, syntax, trees]

type
  Node = TreeNode[NodeKind]
  Context = object
    addrType: Node

using
  c: Context
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var ChangeSet[NodeKind]

proc lowerExprs(c; tree; n; bu)

proc lowerOffset(c; tree; n; bu) =
  let (base, idx, scale) = tree.triplet(n)
  # turn (Offset base idx scale) into:
  # * (Add typ base idx) when there's no scaling
  # * (Add typ base (Mul typ idx scale)) when there's scaling
  bu.modifyTree(tree, n, Add, m):
    bu.insert(m, base, c.addrType)
    c.lowerExprs(tree, base, bu)
    if tree.getInt(scale) == 1:
      # no scaling is needed
      c.lowerExprs(tree, idx, bu)
    else:
      let t = bu.openTree(tree, idx):
        c.lowerExprs(tree, idx, bu)
      bu.replace(idx,
        bu.buildTree(
          tree(Mul, node(c.addrType),
            embed(t),
            node(tree[scale]))))
    bu.remove(m, scale)

proc lowerExprs(c; tree; n; bu) =
  case tree[n].kind
  of Nil:
    # represented as zero
    bu.replace(n, Node(kind: IntVal, val: 0))
  of Ptr:
    bu.replace(n, c.addrType)
  of Offset:
    c.lowerOffset(tree, n, bu)
  of Reinterp:
    let (to, frm, val) = triplet(tree, n)
    let t = bu.openTree(tree, val):
      c.lowerExprs(tree, val, bu)

    if (tree[to].kind == Ptr and tree[frm] == c.addrType) or
       (tree[frm].kind == Ptr and tree[to] == c.addrType):
      # obsolete reinterpretation, remove it
      bu.replace(n, t)
    else:
      if tree[to].kind == Ptr:
        bu.replace(to, c.addrType)
      if tree[frm].kind == Ptr:
        bu.replace(frm, c.addrType)
      bu.replace(val, t)
  else:
    for it in tree.filter(n, {Nil, Ptr, Offset, Reinterp}):
      c.lowerExprs(tree, it, bu)

proc lower*(tree; ptrSize: Positive): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of a pointer value.
  let
    c = Context(addrType: Node(kind: UInt, val: ptrSize.uint32))
    (types, globals, procs) = tree.triplet(NodeIndex(0))

  # update all inline types in signatures:
  for it in tree.filter(types, {Ptr}):
    result.replace(it, c.addrType)

  # update all inline ptr types in global defs:
  for it in tree.filter(globals, {Ptr}):
    result.replace(it, c.addrType)

  for it in tree.items(procs):
    if tree[it].kind == ProcDef:
      c.lowerExprs(tree, it, result)
