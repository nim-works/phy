## Implements some helper and utility routines for working with NimNode AST.

import std/[macros]

proc copyLineInfoForTree*(n, info: NimNode) =
  copyLineInfo(n, info)
  for i in 0..<n.len:
    copyLineInfoForTree(n[i], info)

proc makeError*(msg: string, info: NimNode): NimNode =
  ## Creates an error statement reporting `msg` at the given source location.
  let it = nnkExprColonExpr.newTree(ident"error", newStrLitNode(msg))
  result = nnkPragma.newTree(it)
  copyLineInfoForTree(result, info)
