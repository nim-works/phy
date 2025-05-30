## Implements the nanopass framework, which is a collection of macro DSLs for
## defining intermediate languages (their syntax and grammar) and passes.

# TODO:
# * implement the DSL for pass definitions
# * add a "compiler definition" macro

import
  std/[macros, sets, strformat, tables]

type
  Elem = object
    mvar: string
    typ: string
      ## the actual type
    repeat: bool

  Form = object
    tag: string
    elems: seq[Elem]

  NamedForm = object
    names: seq[string]
      ## gives a name to each element of the form
    form: int
      ## reference to the form

  NonTerminal = object
    mvars: seq[string]
      ## the meta-variables for ranging over the productions
    vars: seq[string]
      ## meta-variables used as productions
    forms: seq[NamedForm]
      ## forms used as productions

  LangDef = object
    terminals: Table[string, string]
      ## name -> type. The terminals of the language
    nterminals: Table[string, NonTerminal]
      ## the non-terminals of the language
    forms: seq[Form]
      ## all forms used in productions
    tags: Table[string, uint8]
      ## associates an integer ID with each tag

  NonTerminalDef = object
    ## Pre-processed non-terminal definition.
    name: NimNode
    sub: seq[NimNode]
    add: seq[NimNode]

template findIt[T](s: seq[T], predicate: untyped): untyped =
  ## Version of ``find`` that allows providing an inline predicate,
  ## evaluated for every checked item.
  var r = -1
  block:
    for i, it {.inject.} in s.pairs:
      if predicate:
        r = i
  r

proc `==`(x, y: Elem): bool =
  x.mvar == y.mvar and x.repeat == y.repeat

proc `==`(x, y: Form): bool =
  ## Compares `x` and `y`, which must belong to the same language, for equality.
  x.tag == y.tag and x.elems == y.elems

proc checkName(target: LangDef, vars: Table[string, string], name: string,
               info: NimNode) =
  if name in target.terminals:
    error(fmt"terminal with name {name} already exists", info)
  elif name in target.nterminals:
    error(fmt"non-terminal with name {name} already exists", info)
  elif name in vars:
    error(fmt"'{name}' is already used by a meta-variable for '{vars[name]}'", info)

proc parseForm(vars: Table[string, string], n: NimNode): (seq[string], Form) =
  n[0].expectKind nnkIdent
  var form = Form(tag: n[0].strVal)

  for i in 1..<n.len:
    var elem = Elem()
    var it = n[i]
    if it.kind == nnkPrefix and it[0].eqIdent("..."):
      elem.repeat = true
      it = it[1]

    it.expectKind nnkIdent
    let name = it.strVal
    var e = name.high
    # to get the type, trim trailing numbers and a single underscore:
    while e >= 0 and name[e] in {'0'..'9'}:
      dec e

    if e >= 0 and name[e] == '_':
      dec e

    elem.mvar = name[0..e]
    if elem.mvar notin vars:
      error(fmt"no meta-var with name '{elem.mvar}' exists", it)

    elem.typ = vars[elem.mvar]
    form.elems.add elem
    result[0].add name
  result[1] = form

proc parseRawForm(n: NimNode): Form =
  ## Parses a raw form (a form without name information) from the given AST.
  n[0].expectKind nnkIdent
  result.tag = n[0].strVal

  for i in 1..<n.len:
    var elem = Elem()
    var it = n[i]
    if it.kind == nnkPrefix and it[0].eqIdent("..."):
      elem.repeat = true
      it = it[1]

    it.expectKind nnkIdent
    elem.mvar = it.strVal
    result.elems.add elem

proc addForm(def: var LangDef, form: Form): int =
  def.forms.add form
  result = def.forms.high

proc computeTags(def: var LangDef) =
  ## Populates the tag table.
  var next: uint8
  for tag in def.tags.values:
    next = max(tag + 1, next)
  # ^^ while simple, this does waste ID space

  for it in def.forms.items:
    if it.tag notin def.tags:
      # TODO: handle overflow
      def.tags[it.tag] = next
      inc next

proc buildLanguage(add, sub: seq[NimNode],
                   def: seq[NonTerminalDef],
                   base: LangDef, info: NimNode): LangDef =
  ## The center-piece of language definition construction. Constructs a
  ## language definition by applying the diff for terminals (`add` and `sub`)
  ## and non- terminals (`def`) to `base`. `info` is used for error reporting.
  var base = base
  # ^^ base is modified in-place because it makes the implementation easier

  # constructing a language while taking into account a base language is fairly
  # involved. The process is separated into two phases:
  # 1. inherit; carry over everything not explicitly removed
  # 2. extension; make the additions

  proc processTerminal(n: NimNode): (string, string) =
    n.expectKind nnkCall
    n.expectLen 2
    n[0].expectKind nnkIdent
    n[1].expectKind nnkIdent
    result = (n[0].strVal, n[1].strVal)

  # apply the terminal removals and carry over the remaining ones:
  for it in sub.items:
    let (name, typ) = processTerminal(it)
    if name notin base.terminals or base.terminals[name] != typ:
      error("terminal does not exist in the base language", it)
    base.terminals.del(name)

  result.terminals = base.terminals

  var vars: Table[string, string]
  for it in result.terminals.keys:
    vars[it] = it

  proc removeProd(def: var LangDef, n: NimNode, to: string) =
    case n.kind
    of nnkCall:
      let f = def.forms.find(parseRawForm(n))
      let idx = def.nterminals[to].forms.findIt(it.form == f)
      if idx == -1:
        error(fmt"given form is not a production of '{to}'", n)
      def.nterminals[to].forms.delete(idx)
    of nnkIdent:
      let idx = def.nterminals[to].vars.find(n.strVal)
      if idx == -1:
        error(fmt"given form is not a production of '{to}'", n)
      def.nterminals[to].vars.delete(idx)
    else:
      error(fmt"unexpected syntax: {n.kind}", n)

  # apply the production removals to the base language:
  for it in def.items:
    it.name.expectKind nnkCall
    it.name[0].expectKind nnkIdent
    let name = it.name[0].strVal
    if it.sub.len > 0:
      if name notin base.nterminals:
        error(fmt"base language has no non-terminal with name '{name}'",
              it.name)

      for prod in it.sub.items:
        removeProd(base, prod, name)

      if it.add.len == 0 and
         base.nterminals[name].vars.len == 0 and
         base.nterminals[name].forms.len == 0:
        # the non-terminal is and will stay empty, remove it
        base.nterminals.del(name)

    if name in base.nterminals:
      # remove the old names:
      base.nterminals[name].mvars.shrink(0)

  # update the var list with the to-be-inherited non-terminal meta-vars:
  for name, it in base.nterminals.pairs:
    for n in it.mvars.items:
      vars[n] = name

  # only now set the new meta-variable names for inherited non-terminals:
  for it in def.items:
    let name = it.name[0].strVal
    if name in base.nterminals:
      for i in 1..<it.name.len:
        let mname = it.name[i].strVal
        checkName(base, vars, mname, it.name[i])
        base.nterminals[name].mvars.add mname
        vars[mname] = name

  proc checkForm(def: LangDef, vars: Table[string, string], form: Form,
                 info: NimNode) =
    for i, it in form.elems.pairs:
      if it.mvar in vars:
        if vars[it.mvar] != it.typ:
          error(fmt"cannot inherit '{form}'; '{it.mvar}' changed its meaning",
                info)
      else:
        error(fmt"cannot inherit '{form}'; '{it.mvar}' was removed", info)

  # after all that setup, the productions can finally be inherited:
  for name, it in base.nterminals.pairs:
    var res = it
    # inherit the forms and patch references:
    for f in res.forms.mitems:
      # make sure the forms are still valid after the previous removals/renames
      checkForm(base, vars, base.forms[f.form], info)
      var idx = result.forms.find(base.forms[f.form])
      if idx == -1:
        idx = result.addForm(base.forms[f.form])
      f.form = idx

    # check the meta-vars:
    for v in res.vars.items:
      if v notin vars:
        error(fmt"cannot inherit '{name}'; '{v}' (used as a production of '{name}') was removed",
              info)

    result.nterminals[name] = res

  # ---- phase 2: make all additions
  for it in add.items:
    let (name, typ) = processTerminal(it)
    checkName(result, vars, name, it)
    result.terminals[name] = typ
    vars[name] = name

  proc addProd(def: var LangDef, n: NimNode, to: string) =
    case n.kind
    of nnkCall:
      let (names, form) = parseForm(vars, n)
      var idx = def.forms.find(form)
      if idx == -1:
        # register the form first
        idx = def.addForm(form)
      if def.nterminals[to].forms.findIt(it.form == idx) != -1:
        error(fmt"production is already part of '{to}'", n)
      def.nterminals[to].forms.add NamedForm(names: names, form: idx)
    of nnkIdent:
      let name = n.strVal
      if name notin vars:
        error(fmt"no meta-variable with name '{name}'", n)
      def.nterminals[to].vars.add name
    else:
      error(fmt"unexpected syntax: {n.kind}", n)

  # register the non-terminals first:
  for it in def.items:
    let name = it.name[0].strVal
    if it.add.len > 0 and name notin base.nterminals:
      # it's a new non-terminal
      checkName(result, vars, name, it.name)
      var nt = NonTerminal()
      for i in 1..<it.name.len:
        checkName(result, vars, it.name[i].strVal, it.name[i])
        nt.mvars.add it.name[i].strVal
        vars[it.name[i].strVal] = name

      result.nterminals[name] = nt

  # add the productions:
  for it in def.items:
    let name = it.name[0].strVal
    if it.add.len > 0:
      for a in it.add.items:
        addProd(result, a, name)

  # TODO: implement tag ID computation for terminals
  # TODO: re-use tag IDs from the base language
  computeTags(result)

proc makeLanguage(body: NimNode): LangDef =
  ## Creates a language definition from the ``defineLanguage`` DSL code.
  body.expectMinLen 1
  var add: seq[NimNode]
  var def: seq[NonTerminalDef]

  # second pass: process the productions
  proc extract(n: NimNode, list: var seq[NimNode]) =
    case n.kind
    of nnkInfix:
      if n[0].eqIdent("|"):
        n.expectLen 3
        extract(n[1], list)
        extract(n[2], list)
      else:
        error("expected '|'", n[0])
    of nnkCall, nnkIdent:
      list.add n
    else:
      error("unexpected syntax: " & $n.kind, n)

  for it in body.items:
    case it.kind
    of nnkInfix:
      if it[0].eqIdent("::="):
        var nt = NonTerminalDef(name: it[1])
        extract(it[2], nt.add)
        def.add nt
        continue
    of nnkCall:
      add.add it
      continue
    else:
      discard "report an error below"

    error("items must be of the form `a in b`, or `a ::= ...`", it)

  # to keep the implementation simple, a non-extension language is treated
  # internally as an empty language definition being extended
  buildLanguage(add, @[], def, default(LangDef), body)

proc makeLanguage(base: LangDef, body: NimNode): LangDef =
  ## Creates a language definition from the ``defineLanguage`` DSL code
  ## and `base`.
  var add, sub: seq[NimNode]
  var def: seq[NonTerminalDef]

  proc extract(n: NimNode, add, sub: var seq[NimNode]) =
    case n.kind
    of nnkPrefix:
      if n[0].eqIdent("+"):
        add.add n[1]
      elif n[0].eqIdent("-"):
        sub.add n[1]
      else:
        error("expected `+` or `-`", n[0])
    of nnkInfix:
      if n[0].eqIdent("|"):
        n.expectLen 3
        extract(n[1], add, sub)
        extract(n[2], add, sub)
      else:
        error("expected '|'", n[0])
    else:
      error("unexpected syntax: " & $n.kind, n)

  for it in body.items:
    var handled = false
    case it.kind
    of nnkInfix:
      if it[0].eqIdent("::="):
        it.expectLen 3
        var nt = NonTerminalDef(name: it[1])
        nt.name.expectKind nnkCall
        extract(it[2], nt.add, nt.sub)
        def.add nt
        handled = true
    of nnkPrefix:
      if it[0].eqIdent("-"):
        sub.add it[1]
        handled = true
      elif it[0].eqIdent("+"):
        add.add it[1]
        handled = true
    of nnkCall:
      # non-terminal with no change in productions
      def.add NonTerminalDef(name: it)
      handled = true
    else:
      discard

    if not handled:
      error("expected `-a`, `+a`, or `a(...) ::= ...`", it[0])

  buildLanguage(add, sub, def, base, body)

macro defineLanguage*(name, body: untyped) =
  ## Creates a language definitions and binds it to a const symbol with the
  ## given name.
  body.expectKind nnkStmtList
  body.expectMinLen 1
  let p = bindSym"makeLanguage"
  let q = bindSym"quote"
  if body[0].kind == nnkCommentStmt:
    let filtered = body[1..^1]
    result = nnkConstSection.newTree(
      nnkConstDef.newTree(name,
        newEmptyNode(),
        quote do: `p`(`q` do: `filtered`)),
      body[0])
  else:
    result = nnkConstSection.newTree(
      nnkConstDef.newTree(name,
        newEmptyNode(),
        quote do: `p`(`q` do: `body`)))

macro defineLanguage*(name, base, body: untyped) =
  ## Creates a language definition, extending `base`, and binds it to a const
  ## symbol with the given name. Extension doesn't imply a direction in this
  ## context.
  body.expectKind nnkStmtList
  body.expectMinLen 1
  let p = bindSym"makeLanguage"
  let q = bindSym"quote"
  if body[0].kind == nnkCommentStmt:
    let filtered = nnkStmtList.newTree(body[1..^1])
    result = nnkConstSection.newTree(
      nnkConstDef.newTree(name,
        newEmptyNode(),
        quote do: `p`(`base`, `q` do: `filtered`)),
      body[0])
  else:
    result = nnkConstSection.newTree(
      nnkConstDef.newTree(name,
        newEmptyNode(),
        quote do: `p`(`base`, `q` do: `body`)))
