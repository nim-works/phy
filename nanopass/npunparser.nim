## Implements the routines for unparsing an ASTs back into S-expressions.

# TODO: instead of assembling a S-expression directly, the unparser should
#       emit a stream of S-expression tokens (ideally as an iterator, but's
#       that not really possible today, at least in an efficient manner)
# TODO: render and store the unexpected node/tree alongside their
#       corresponding error node

import std/[intsets, macros, tables, typetraits]
import experimental/[sexp]
import nanopass/[asts, nplang]

from nanopass/nppass import get

type
  Ctx = object
    ## The unparsing context object.
    pos: int ## current node position
    records: seq[IntSet]
      ## for each record type, keeps track of the already-defined records

proc nameToIndex[L; Name: static string](): int {.compileTime.} =
  ## Turns a record type name to the index of the corresponding set in
  ## `Ctx.records`.
  var i = 0
  var tmp: L
  # the index being stable across compilation is not necessary
  for f in fields(tmp):
    when f is RecordRef:
      when typeof(f).N == Name:
        if true:
          return i
      inc i

proc unparse[N: static string, S](ast: Ast[auto, S], c: var Ctx): SexpNode

proc unparse[N: static string, L](ast: Ast[L, auto], c: var Ctx, id: int,
                                  tup: tuple): SexpNode =
  ## Unparses the nanopass record `tup`. The full record is only emitted for
  ## the first occurrence - only the ID is emitted for all further occurrences.
  if containsOrIncl(c.records[static nameToIndex[L, N]()], id):
    result = newSList([newSSymbol(":record"), newSSymbol(N), newSInt(id)])
  else:
    result = newSList()
    result.add newSSymbol(":record-def")
    result.add newSSymbol(N)
    result.add newSInt(id)
    for name, val in fieldPairs(tup):
      let node =
        when val is Value:
          toSexp(unpack(ast.storage[], val.index, typeof(val).T))
        elif val is RecordRef:
          unparse[typeof(val).N](ast, c, val.id.int, get(ast, val))
        elif val is Metavar:
          let prev = c.pos
          c.pos = val.index.int
          let r = unparse[typeof(val).N](ast, c)
          c.pos = prev
          r
        else:
          {.error: "unreachable".}

      result.add newSList([newSSymbol(name), node])

macro unparse(def: static LangInfo, nterm: static string, ast, c: untyped) =
  ## Unparses the non-terminal with name `nterm` from the given language at
  ## the current cursor position `pos`.
  let id = def.map[nterm]
  var caseStmt = nnkCaseStmt.newTree(quote do: `ast`.tree.nodes[`c`.pos].kind)

  proc genForType(def: LangInfo, typ: LangType): NimNode =
    case typ.kind
    of tkTerminal:
      let name = ident(typ.name)
      quote do:
        inc `c`.pos
        toSexp(unpack(`ast`.storage[], `ast`.tree.nodes[`c`.pos - 1].val, `name`))
    of tkRecord:
      let unparse = bindSym"unparse"
      let mvar = ident(typ.mvar)
      let tmp = genSym("id")
      let name = typ.name
      quote do:
        let `tmp` = `ast`.tree.nodes[`c`.pos].val.int
        inc `c`.pos
        `unparse`[`name`](`ast`, `c`, `tmp`, `ast`.records.`mvar`[`tmp`])
    of tkNonTerminal:
      let unparse = bindSym"unparse"
      let name = typ.name
      quote do:
        `unparse`[`name`](`ast`, `c`)

  # form renderers:
  for it in def.types[id].forms.items:
    var body = nnkStmtList.newTree()
    let name = def.forms[it].name
    body.add quote do:
      let len {.used.} = `ast`.tree.nodes[`c`.pos].val.int
      inc `c`.pos
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

  # rendering for embedded types:
  for it in def.types[id].sub.items:
    let body = nnkAsgn.newTree(ident"result", genForType(def, def.types[it]))
    case def.types[it].kind
    of tkTerminal:
      caseStmt.add nnkOfBranch.newTree(newIntLitNode(def.types[it].ntag), body)
    of tkRecord:
      caseStmt.add nnkOfBranch.newTree(newIntLitNode(def.types[it].rtag), body)
    of tkNonTerminal:
      let ofb = nnkOfBranch.newTree()
      for tag in ntags(def, def.types[it]).items:
        ofb.add newIntLitNode(tag)
      ofb.add body
      caseStmt.add ofb

  # for robustness, and to make spotting of problems easier, render unexpected
  # nodes as errors
  caseStmt.add nnkElse.newTree(quote do:
    result = newSList(
      [newSSymbol(":error"), newSInt(int `ast`.tree.nodes[`c`.pos].kind)])
    `c`.pos = `ast`.tree.next(NodeIndex `c`.pos).int)
  result = caseStmt

proc unparse[N: static string, S](ast: Ast[auto, S], c: var Ctx): SexpNode =
  ## Unparses the non-terminal at `pos`, returning the corresponding
  ## S-expression. Implemented outside the main macro to facilitate caching
  ## of the generic's instantiation.
  mixin idef
  unparse(idef(typeof(ast).L), N, ast, c)

proc unparse*[L, S, N](ast: Ast[L, S], at: Metavar[L, N]): SexpNode =
  ## Unparses the production at the given position `at`, returning it as a
  ## self-contained S-expression.
  var c = Ctx(pos: at.index.int)
  c.records.newSeq(tupleLen(L.meta.records))
  unparse[N](ast, c)
