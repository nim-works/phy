## Implements the `defineCompiler <#defineCompiler,untyped,varargs[untyped]>`_
## macro, for defining nanopass compilers, which are compositions of passes.

import std/macros

macro defineCompiler*(name, start, names: untyped) =
  ## Generates a compiler procedures, running the provided passes in
  ## sequence. Interim implementation.
  var prevAst = ident"ast"
  var prevPos = ident"it"
  let body = newStmtList()
  for it in names.items:
    let tmp = genSym()
    if it.kind == nnkIdent:
      let name = it.strVal
      body.add quote do: echo "-- ", `name`
      body.add newLetStmt(tmp, quote do: `it`(`prevAst`, `prevPos`))
    else:
      let g = it
      g.insert 1, prevPos
      g.insert 1, prevAst
      let name = it[0].strVal
      body.add quote do: echo "-- ", `name`
      body.add newLetStmt(tmp, g)
    prevAst = quote do: `tmp`[0]
    prevPos = quote do: `tmp`[1]
  result = quote do:
    proc `name`(ast: Ast[`start`, Literals], it: `start`.meta.entry): auto =
      `body`
      result = (`prevAst`, `prevPos`)
