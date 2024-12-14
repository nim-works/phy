## Simple stack allocation pass. Adds a frame pointer local to all procedures
## that use stack memory and turns blob locals into stack locations
## (|L2| -> |L1|).

import
  passes/[changesets, spec, trees]

using
  tree: PackedTree[NodeKind]

proc lower*(tree; ptrSize: int): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of a pointer value.
  discard
