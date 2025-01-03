## Removes `Blob` types and turns all identified numeric types into inline
## types (|L1| -> |L0|).

import
  std/[tables],
  passes/[changesets, spec, trees]

proc lower*(tree: PackedTree[NodeKind]): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var map = initTable[uint32, uint32]()
    ## maps old signature type IDs to the new ones

  template lookup(id: uint32): untyped =
    tree[tree.child(0), id]

  let (types, globals, procs) = tree.triplet(NodeIndex(0))

  result.modifyTree tree, types, m:
    var num = 0'u32
    for i, n in tree.pairs(types):
      if tree[n].kind == ProcTy:
        # inline the parameter types:
        for it in tree.items(n):
          if tree[it].kind == Type:
            result.replace it, lookup(tree[it].val)

        map[i.uint32] = num
        inc num
      else:
        # all other types are either inlined later or not used
        result.remove(m, n)

  for n in tree.filter(globals, {Type}):
    # note: there cannot be references to signatures in global defs
    result.replace n, lookup(tree[n].val)

  for n in tree.filter(procs, {Type}):
    let id = tree[n].val
    map.withValue id, val:
      if val[] != id:
        # don't replace the node if nothing would change
        result.replace n, TreeNode[NodeKind](kind: Type, val: val[])
    do:
      # if not a signature, the type must be a numeric type
      result.replace n, lookup(id)
