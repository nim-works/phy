## Implements routines and helpers for debugging and rendering packed trees.

import
  std/[strutils],
  experimental/[sexp],
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

proc toPretty(result: var string, t: PackedTree, n: NodeIndex, indent: int) =
  mixin isAtom
  if isAtom(t[n].kind):
    result.add $toSexp(t, n)
  else:
    result.add "("
    result.add $t[n].kind

    let L = t.len(n)
    var
      n = t.child(n, 0)
      i = 0

    # all simple nodes can be placed on the same line as the parenthesis
    while i < L and (isAtom(t[n].kind) or t.len(n) == 0):
      result.add(" ")
      toPretty(result, t, n, indent)
      inc i
      n = t.next(n)

    let isMultiLine = i < L
    # the rest goes onto new lines:
    while i < L:
      result.add "\n"
      result.add repeat("  ", indent + 1)
      toPretty(result, t, n, indent + 1)
      inc i
      n = t.next(n)

    if isMultiLine:
      result.add "\n"
      result.add repeat("  ", indent)
    result.add ")"

proc pretty*(t: PackedTree, n: NodeIndex): string =
  ## Returns a multi-line textual S-expression representation of `t`.
  toPretty(result, t, n, 0)
