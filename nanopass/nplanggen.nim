## Implements the macros and routines handling the generative part of
## language definition.

import std/[genasts, macros, tables]
import nanopass/[asts, nplang, nplangdef, nppatterns]

macro makeLanguageType(def: static LangDef, typName: untyped) =
  ## Creates the type representing the language defined by `def`. This is the
  ## type the nanopass-framework user passes around.
  ##
  ## The type also stores various information about the language that are
  ## needed by the pass-related macros, encoded as types.
  let fields = nnkRecList.newTree()
  # the metavars are at top level of the type, for easy access by
  # the programmer
  let mvar = bindSym"Metavar"
  for name, it in def.terminals.pairs:
    fields.add newIdentDefs(ident(name),
      nnkBracketExpr.newTree(bindSym"Value", ident(it.typ)))
  for name, it in def.nterminals.pairs:
    for m in it.mvars.items:
      fields.add newIdentDefs(ident(m),
        nnkBracketExpr.newTree(
          mvar,
          ident(typName.strVal),
          newStrLitNode(name)))

  let ntType = nnkTupleTy.newTree()
  let (csym, fsym, vsym) = (bindSym"PChoice", bindSym"PForm", bindSym"Value")
  # add the descriptions for the non-terminals
  for name, nt in def.nterminals.pairs:
    let ln = ident(typName.strVal)
    var p = ident"void"
    for f in nt.forms.items:
      let id = def.forms[f.semantic].id
      p = quote do:
        `csym`[`p`, `fsym`[`id`]]

    for v in nt.vars.items:
      if v in def.terminals:
        let id = ident(def.terminals[v].typ)
        p = quote do:
          `csym`[`p`, `vsym`[`id`]]
      else:
        let id = ident(v)
        p = quote do:
          `csym`[`p`, `ln`.`id`]

    ntType.add newIdentDefs(ident(name), p)

  # everything meant for internal use is stored in an anonymous record in
  # the `meta` field, preventing name clashes and the fields showing up
  # in auto-complete suggestions
  let metaType = nnkTupleTy.newTree(
    newIdentDefs(ident"entry",
      nnkBracketExpr.newTree(mvar,
        ident(typName.strVal),
        newStrLitNode(def.entry))),
    newIdentDefs(ident"nt", ntType))

  # create the terminal->tag map:
  let tup = nnkTupleConstr.newTree()
  for it in def.terminals.values:
    let n = it.tag
    tup.add nnkTupleConstr.newTree(
      ident(it.typ),
      nnkBracketExpr.newTree(bindSym"Static", newIntLitNode(n)))

  metaType.add newIdentDefs(ident"term_map", tup)

  fields.add newIdentDefs(ident"meta", metaType)

  result = nnkTypeSection.newTree(
    nnkTypeDef.newTree(
      typName,
      newEmptyNode(),
      nnkObjectTy.newTree(
        newEmptyNode(),
        newEmptyNode(),
        fields)))

macro genHelpers(typ, a, b: untyped) =
  ## Generates the helper templates `def` and `idef`, which are used for
  ## retrieving the `LangDef` and `LangInfo` instance for a language type,
  ## respectively.
  let (def, info) = (bindSym"LangDef", bindSym"LangInfo")
  quote do:
    template def(_: typedesc[`typ`]): `def` = `a`
    template idef(_: typedesc[`typ`]): `info` = `b`

proc defineLanguageImpl*(name, base, body: NimNode): NimNode =
  body.expectKind nnkStmtList
  body.expectMinLen 1
  if body[0].kind == nnkCommentStmt:
    body.del(0)

  let setup1 =
    if base.isNil:
      genAst(body): makeLanguage(quote do: body)
    else:
      genAst(body, base): makeLanguage(def(base), quote do: body)
  result = genAst(setup1, name):
    const
      def = setup1
      tmp = buildLangInfo(def)
    makeLanguageType(def, name)
    genHelpers(name, def, tmp)
