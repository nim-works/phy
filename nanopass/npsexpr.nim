## Implements the macros for converting between ASTs and S-expressions.

# TODO: instead of assembling a S-expression directly, the renderer should
#       emit a stream of S-expression tokens (ideally as an iterator, but's
#       that not really possible today, at least in an efficient manner)

import std/[macros, tables]
import nanopass/[nplang, helper]
import passes/[trees]

const
  Inp = ident"tree" ## name of the input AST parameter
  Pos = ident"pos" ## name of the position parameter

macro genRenderer(def: static LangInfo, nterm: static string) =
  ## Generates the rendering logic for the non-terminal with name `nterm`.
  let id = def.map[nterm]
  var caseStmt = nnkCaseStmt.newTree(quote do: `Inp`.tree.nodes[`Pos`].kind)

  proc genForType(def: LangInfo, typ: LangType): NimNode =
    case typ.terminal
    of true:
      let name = ident(typ.name)
      quote do:
        inc `Pos`
        toSexp(unpack(`Inp`.storage[], `Inp`.tree.nodes[`Pos` - 1].val, `name`))
    of false:
      let name = typ.name
      quote do:
        render[`name`](`Inp`, `Pos`)

  # form renderers:
  for it in def.types[id].forms.items:
    var body = nnkStmtList.newTree()
    let name = def.forms[it].name
    body.add quote do:
      let len {.used.} = `Inp`.tree.nodes[`Pos`].val.int
      inc `Pos`
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

  caseStmt.add nnkElse.newTree(newCall(bindSym"unreachable"))
  result = caseStmt

macro rendererImpl(x: untyped, def: untyped) =
  ## The actual implementation of the ``renderer`` macro.
  let gen = bindSym("genRenderer", brClosed)
  let tree = genSym("tree")
  def.params[1][^2] = bindSym"NodeIndex"
  def.params.insert(1,
    newIdentDefs(tree, quote do: Ast[typeof(`x`).L, Literals]))
  def.body = quote do:
    type Src = typeof(`x`).L
    proc render[N: static string](`Inp`: Ast[Src, Literals],
                                  pos: var int): SexpNode =
      `gen`(idef(Src), N)

    var pos = x.int
    render[typeof(`x`).N](`tree`, pos)

  result = def

macro renderer*(def: untyped): untyped =
  ## A procedure macro that generates a body for rendering an non-terminal at
  ## a given position into an S-expression representation. The prototype must
  ## have the following form:
  ##
  ## .. code-block:: nim
  ##
  ##   proc name(x: Metavar[L, ...]): SexpNode
  ##
  ## and is expanded into:
  ##
  ## .. code-block:: nim
  ##
  ##   proc name(_: Ast[L, Literals], x: NodePos): SexpNode = ...
  ##
  ## Terminals are rendered via ``toSexpr`` (with signature
  ## ``proc(x: T): SexpNode``) provided by the callsite.
  if def.kind != nnkProcDef or def.body.kind != nnkEmpty:
    error(".renderer must be applied to a procedure declaration")
  elif def.params.len == 2 and def.params[1].len == 1:
    error("prototype must have exactly one parameter")

  let
    typ = def.params[1][^2]
    impl = bindSym("rendererImpl")
    error = makeError("parameter type must a `Metavar`", typ)

  result = quote do:
    when `typ` is Metavar:
      `impl`(`typ`, `def`)
    else:
      `error`
