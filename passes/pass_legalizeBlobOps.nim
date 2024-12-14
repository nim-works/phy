## Turns loads, stores, and assignments of blob types into blit copies
## (|L3| -> |L3|).

import
  passes/[changesets, spec, trees]

using
  tree: PackedTree[NodeKind]

proc lower*(tree): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  discard
