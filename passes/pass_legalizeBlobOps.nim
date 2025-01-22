## Turns loads, stores, and assignments of blob types into blit copies
## (|L3| -> |L3|).

import
  passes/[changesets, syntax, trees],
  vm/utils

using
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var ChangeSet[NodeKind]

proc size(tree; n): uint32 =
  case tree[n].kind
  of Blob: tree[n, 0].val
  of Type: size(tree, tree.child(tree.child(0), tree[n].val))
  else: unreachable()

proc isBlob(tree; n): bool =
  case tree[n].kind
  of Blob: true
  of Type: tree[tree.child(0), tree[n].val].kind == Blob
  of Int, UInt, Float: false
  else:    unreachable()

proc prepareOperand(tree; n; bu): VirtualTree =
  ## (Copy a) -> (Addr a)
  ## (Load typ a) -> a
  case tree[n].kind
  of Copy: bu.buildTree tree(Addr, embed(tree.child(n, 0)))
  of Load: toVirtual tree.child(n, 1)
  else:    unreachable($tree[n].kind)

proc lowerProc(tree; n; bu) =
  let (_, locals, body) = tree.triplet(n)

  for it in tree.filter(body, {Store, Asgn}):
    case tree[it].kind
    of Store:
      let (typ, x, y) = tree.triplet(it)
      if isBlob(tree, typ):
        # (Store typ x y) -> (Blit x y' size)
        bu.replace it:
          bu.buildTree:
            tree(Blit,
              embed(x),
              embed(prepareOperand(tree, y, bu)),
              node(IntVal, size(tree, typ)))
    of Asgn:
      let (x, y) = tree.pair(it)
      let typ = tree.child(locals, tree[x].val)
      if isBlob(tree, typ):
        # (Asgn x y) -> (Blit (Addr x) y' size)
        bu.replace it:
          bu.buildTree:
            tree(Blit,
              tree(Addr, embed(x)),
              embed(prepareOperand(tree, y, bu)),
              node(IntVal, size(tree, typ)))
    else:
      unreachable()

proc lower*(tree): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      lowerProc(tree, it, result)
