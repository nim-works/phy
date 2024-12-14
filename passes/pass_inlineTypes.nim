## Removes `Blob` types and turns all identified numeric types into inline
## types (|L1| -> |L0|).

import
  passes/[changesets, spec, trees]

using
  tree: PackedTree[NodeKind]

proc lower*(tree): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  discard
