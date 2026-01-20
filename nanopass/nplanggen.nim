## Implements the macros and routines handling the generative part of
## language definition.

import std/[genasts, macros, tables]
import nanopass/[asts, nplang, nplangdef, nppatterns]

macro makeMetaType(def: static LangInfo, typname: untyped): typedesc =
  ## Expands to the tuple type storing the various internal-only information
  ## about a language.
  result = nnkTupleTy.newTree()

  let (csym, fsym) = (bindSym"PChoice", bindSym"PForm")
  let nonTerminals = nnkTupleTy.newTree()
  let terminals = nnkTupleConstr.newTree()
  let recMap = nnkTupleConstr.newTree()
  let records = nnkTupleTy.newTree()

  for typ in def.types.items:
    case typ.kind
    of tkTerminal:
      terminals.add nnkTupleConstr.newTree(
        ident(typ.name),
        nnkBracketExpr.newTree(bindSym"Static", newIntLitNode(typ.ntag)))
    of tkRecord:
      recMap.add nnkTupleConstr.newTree(
        newDotExpr(copyNimTree(typName), ident(typ.mvar)),
        nnkBracketExpr.newTree(bindSym"Static", newIntLitNode(typ.rtag)))

      let tup = nnkTupleTy.newTree()
      for (name, t) in typ.fields.items:
        tup.add newIdentDefs(ident(name),
          newDotExpr(typName, ident(def.types[t].mvar)))

      # expose under the first meta-var there is for the type
      records.add newIdentDefs(ident(typ.mvar),
        nnkBracketExpr.newTree(ident"seq", tup))
    of tkNonTerminal:
      let ln = ident(typName.strVal)
      var p = ident"void"
      for f in typ.forms.items:
        let id = def.forms[f].ntag
        p = quote do:
          `csym`[`p`, `fsym`[`id`]]

      for v in typ.sub.items:
        let id = ident(def.types[v].mvar)
        p = quote do:
          `csym`[`p`, `ln`.`id`]

      nonTerminals.add newIdentDefs(ident(typ.name), p)

  result.add newIdentDefs(ident"nt", nonTerminals)
  if terminals.len > 0:
    result.add newIdentDefs(ident"term_map", terminals)
  if records.len > 0:
    result.add newIdentDefs(ident"record_map", recMap)

  result.add newIdentDefs(ident"records", records)

macro makeLanguageType(def: static LangDef, info: LangInfo, typName: untyped) =
  ## Creates the type representing the language defined by `def`. This is the
  ## type the nanopass-framework user passes around.
  ##
  ## The type also stores various information about the language that are
  ## needed by the pass-related macros, encoded as types.
  let fields = nnkRecList.newTree()
  # the metavars are at top level of the type, for easy access by
  # the programmer
  let prod = bindSym"Production"
  for name, it in def.terminals.pairs:
    for m in it.mvars.items:
      fields.add newIdentDefs(ident(m),
        nnkBracketExpr.newTree(bindSym"Value", ident(name)))
  for name, it in def.nterminals.pairs:
    for m in it.mvars.items:
      fields.add newIdentDefs(ident(m),
        nnkBracketExpr.newTree(
          prod,
          ident(typName.strVal),
          newStrLitNode(name)))
  for name, it in def.records.pairs:
    for m in it.mvars.items:
      fields.add newIdentDefs(ident(m),
        nnkBracketExpr.newTree(bindSym"RecordRef",
          ident(typName.strVal),
          newStrLitNode(name)))

  # add the entry non-terminal:
  fields.add newIdentDefs(ident"entry",
    nnkBracketExpr.newTree(prod,
      ident(typName.strVal),
      newStrLitNode(def.entry)))

  # everything meant for internal use is stored in an anonymous record in
  # the `meta` field, preventing name clashes and the fields showing up
  # in auto-complete suggestions
  fields.add newIdentDefs(ident"meta",
    newCall(bindSym"makeMetaType", info, typName))

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
    makeLanguageType(def, tmp, name)
    genHelpers(name, def, tmp)
