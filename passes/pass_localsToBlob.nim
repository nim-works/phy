## Turns all non-blob locals that have their address taken into blob locals.
## Goes from |L3| code to |L2| code.

import
  passes/[changesets, spec, trees]

using
  tree: PackedTree[NodeKind]

proc lower*(tree): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  discard
