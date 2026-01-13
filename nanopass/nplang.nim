## Provides the query-focused types representing the language in the nanopass
## framework, as well as the routines for creating instances thereof.

import std/[sequtils, tables]
import nanopass/[nplangdef]

type
  SForm* = object
    ## Semantic-focused representation of a syntax form, optimized for
    ## macro processing.
    name*: string
    ntag*: int
      ## the node tag identifying the form in an AST
    elems*: seq[tuple[typ: int, repeat: bool]]

  TypeKind* = enum
    tkTerminal
    tkRecord
    tkNonTerminal

  LangType* = object
    ## Terminals and non-terminals modeled as types.
    name*: string
    mvar*: string
      ## name of a meta-variable that is used to range over the type
    case kind*: TypeKind
    of tkTerminal:
      ntag*: int
        ## the tag by which a node storing the terminal value is identified
    of tkRecord:
      rtag*: int
        ## the tag by which a node storing the record is identified
      fields*: seq[tuple[name: string, typ: int]]
    of tkNonTerminal:
      sub*: seq[int]
        ## the types part of the union
      forms*: seq[int]
        ## all production forms of the non-terminal

  LangInfo* = object
    ## Representation of a language definition that stores the information in
    ## a way that make it easier to work with for the DSL macros.
    # important: for compilation speed, the AST representation of the data
    # should be as short and concise as possible
    types*: seq[LangType]
    map*: Table[string, int]
      ## maps type and meta-var names to the corresponding type
    forms*: seq[SForm]

  PForm*[I: static int] = object

  Static*[V: static int] = distinct int
    ## Carrier for a compile-time known integer value.

proc buildLangInfo*(def: LangDef): LangInfo =
  ## Creates the pass-centric language representation for `def`.
  result.map = initTable[string, int](4)

  for name, it in def.terminals.pairs:
    result.types.add LangType(
      name: name,
      mvar: it.mvars[0],
      kind: tkTerminal,
      ntag: it.tag
    )
    # add the name-to-type mappings:
    result.map[name] = high(result.types)
    for x in it.mvars.items:
      result.map[x] = high(result.types)

  for name, it in def.nterminals.pairs:
    result.types.add LangType(
      name: name,
      mvar: it.mvars[0],
      kind: tkNonTerminal,
      forms: mapIt(it.forms, it.semantic)
    )
    # add the name-to-type mappings:
    result.map[name] = high(result.types)
    for x in it.mvars.items:
      result.map[x] = high(result.types)

  for name, it in def.records.pairs:
    result.types.add LangType(
      name: name,
      mvar: it.mvars[0],
      kind: tkRecord,
      rtag: it.tag
    )
    # add the name-to-type mappings:
    result.map[name] = high(result.types)
    for x in it.mvars.items:
      result.map[x] = high(result.types)

  # now that all name-to-type mappings are present, add the forms and
  # the subtype info
  for it in def.forms.items:
    result.forms.add SForm(
      name: it.tag,
      ntag: it.id,
      elems: mapIt(it.elems, (result.map[it.typ], it.repeat))
    )

  for name, it in def.nterminals.pairs:
    let id = result.map[name]
    for v in it.vars.items:
      result.types[id].sub.add result.map[v]

  for name, it in def.records.pairs:
    let id = result.map[name]
    for field in it.fields.items:
      result.types[id].fields.add (field.name, result.map[field.typ])

proc ntags*(lang: LangInfo, typ: LangType): seq[int] =
  ## Returns a list with all possible node tags productions of `typ` can have.
  for it in typ.forms.items:
    result.add lang.forms[it].ntag

  for it in typ.sub.items:
    case lang.types[it].kind
    of tkTerminal:
      result.add lang.types[it].ntag
    of tkRecord:
      result.add lang.types[it].rtag
    of tkNonTerminal:
      result.add ntags(lang, lang.types[it])

proc render*(lang: LangInfo, form: SForm): string =
  result.add form.name
  result.add "("
  for i, it in form.elems.pairs:
    if i > 0:
      result.add ", "
    if it.repeat:
      result.add "..."
    result.add lang.types[it.typ].mvar
  result.add ")"
