## Implements some helper and utility routines for working with NimNode AST.

import std/[macros]

proc makeError*(msg: string, info: NimNode): NimNode =
  ## Creates an error statement reporting `msg` at the given source location.
  let it = nnkExprColonExpr.newTree(ident"error", newStrLitNode(msg))
  copyLineInfo(it, info)
  result = nnkPragma.newTree(it)
