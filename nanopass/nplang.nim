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

  LangType* = object
    ## Terminals and non-terminals modeled as types.
    name*: string
    mvar*: string
      ## name of a meta-variable that is used to range over the type
    case terminal*: bool
    of true:
      ntag*: int
        ## the tag with which a node storing the terminal value is identified
    of false:
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
      name: it.typ,
      mvar: name,
      terminal: true,
      ntag: it.tag
    )
    result.map[name] = high(result.types)

  for name, it in def.nterminals.pairs:
    result.types.add LangType(
      name: name,
      mvar: it.mvars[0],
      terminal: false,
      forms: mapIt(it.forms, it.semantic)
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
