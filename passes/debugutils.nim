## Implements routines and helpers for debugging and rendering packed trees.

import
  std/[strutils],
  passes/[trees]

proc render(t: PackedTree, i: NodeIndex, indent: int, result: var string) =
  mixin isAtom
  if i.int >= t.nodes.len:
    # don't crash for malformed trees
    return

  var line = repeat("  ", indent) & $t[i].kind
  if isAtom(t[i].kind):
    line.add " "
    line.addInt t[i].val
    result.add line & '\n'
  else:
    result.add line & '\n'
    # render all child nodes:
    for it in t.items(i):
      render(t, it, indent + 1, result)

proc treeRepr*(t: PackedTree): string =
  ## Returns a multi-line tree representation of `t`. The output is meant to be
  ## usable as test output, and the format should thus stay stable.
  render(t, NodeIndex(0), 0, result)
