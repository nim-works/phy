## Turns `At` and `Field` expressions into flat `Path` expressions, for easier
## processing by later passes (|L5| -> |L4|).

import
  passes/[changesets, spec, trees]

using
  tree: PackedTree[NodeKind]

proc lower*(tree): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  discard
