## Turns all aggregate parameters into pointer parameters and replaces returns
## of aggregate with out parameters (|L4| -> |L3|).

import
  passes/[changesets, spec, trees]

using
  tree: PackedTree[NodeKind]

proc lower*(tree; ptrSize: int): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of a pointer value.
  discard
