## Implements the routines for unparsing an ASTs back into S-expressions.

# TODO: instead of assembling a S-expression directly, the unparser should
#       emit a stream of S-expression tokens (ideally as an iterator, but's
#       that not really possible today, at least in an efficient manner)
# TODO: render and store the unexpected node/tree alongside their
#       corresponding error node

import std/[macros, tables]
import experimental/[sexp]
import nanopass/[asts, nplang]

proc unparse[N: static string, S](ast: Ast[auto, S], pos: var int): SexpNode

macro unparse(def: static LangInfo, nterm: static string, ast, pos: untyped) =
  ## Unparses the non-terminal with name `nterm` from the given language at
  ## the current cursor position `pos`.
  let id = def.map[nterm]
  var caseStmt = nnkCaseStmt.newTree(quote do: `ast`.tree.nodes[`pos`].kind)

  proc genForType(def: LangInfo, typ: LangType): NimNode =
    case typ.terminal
    of true:
      let name = ident(typ.name)
      quote do:
        inc `pos`
        toSexp(unpack(`ast`.storage[], `ast`.tree.nodes[`pos` - 1].val, `name`))
    of false:
      let unparse = bindSym"unparse"
      let name = typ.name
      quote do:
        `unparse`[`name`](`ast`, `pos`)

  # form renderers:
  for it in def.types[id].forms.items:
    var body = nnkStmtList.newTree()
    let name = def.forms[it].name
    body.add quote do:
      let len {.used.} = `ast`.tree.nodes[`pos`].val.int
      inc `pos`
      result = newSList([newSSymbol(`name`)])
    for i, e in def.forms[it].elems.pairs:
      let inner = genForType(def, def.types[e.typ])
      if e.repeat:
        let start = def.forms[it].elems.len - 1
        body.add quote do:
          for _ in `start`..<len:
            result.add `inner`
      else:
        body.add quote do:
          result.add `inner`
    caseStmt.add nnkOfBranch.newTree(newIntLitNode(def.forms[it].ntag), body)

  # rendering for embedded terminals and non-terminals:
  for it in def.types[id].sub.items:
    let body = nnkAsgn.newTree(ident"result", genForType(def, def.types[it]))
    case def.types[it].terminal
    of true:
      caseStmt.add nnkOfBranch.newTree(newIntLitNode(def.types[it].ntag), body)
    of false:
      let ofb = nnkOfBranch.newTree()
      for tag in ntags(def, def.types[it]).items:
        ofb.add newIntLitNode(tag)
      ofb.add body
      caseStmt.add ofb

  # for robustness, and to make spotting of problems easier, render unexpected
  # nodes as errors
  caseStmt.add nnkElse.newTree(quote do:
    result = newSList(
      [newSSymbol(":error"), newSInt(int `ast`.tree.nodes[`pos`].kind)])
    `pos` = `ast`.tree.next(NodeIndex `pos`).int)
  result = caseStmt

proc unparse[N: static string, S](ast: Ast[auto, S], pos: var int): SexpNode =
  ## Unparses the non-terminal at `pos`, returning the corresponding
  ## S-expression. Implemented outside the main macro to facilitate caching
  ## of the generic's instantiation.
  mixin idef
  unparse(idef(typeof(ast).L), N, ast, pos)

proc unparse*[L, S, N](ast: Ast[L, S], at: Metavar[L, N]): SexpNode =
  ## Unparses the production at the given position `at`, returning it as a
  ## self-contained S-expression.
  var pos = at.index.int
  unparse[N](ast, pos)
