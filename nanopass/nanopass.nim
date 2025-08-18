## Implements the nanopass framework, which is a collection of macro DSLs for
## defining intermediate languages (their syntax and grammar) and passes.

# TODO:
# * implement symbol integration
# * implement types integration
# * implement meta-data support
# * add a "compiler definition" macro

import
  std/[genasts, macros, intsets, sequtils, sets, strformat, tables],
  passes/trees,
  asts

export asts

type
  # Core types capturing a defined language
  Elem = object
    ## Element of a form.
    typ: string
      ## the actual type
    repeat: bool

  Form = object
    ## Semantic representation of a syntax form.
    tag: string # TODO: rename to name
    id: int
      ## the integer ID through which a tree node is identified as being an
      ## instance of the form
    elems: seq[Elem]

  OrigForm = object
    ## Source-level-ish representation of a syntax form description.
    vars: seq[string]
      ## the metavars-as-written for the form's elements
    semantic: int
      ## index of the semantic representation

  NonTerminal = object
    mvars: seq[string]
      ## the meta-variables for ranging over the productions
    vars: seq[string]
      ## meta-variables used as productions
    forms: seq[OrigForm]
      ## forms used as productions

  LangDef = object
    ## A checked and pre-processed language definition, carrying enough
    ## source-level information necessary for implementing, e.g., inheritance.
    terminals: Table[string, tuple[typ: string, tag: int]]
      ## the terminals of the language
    nterminals: Table[string, NonTerminal]
      ## the non-terminals of the language
    forms: seq[Form]
      ## all syntax forms present in the language
    entry: string
      ## name of the non-terminal to use as the entry point

type
  # Intermediate types meant to bridge macro language to core types
  ParsedForm = object
    ## A syntax form description as parsed from NimNode AST.
    name: string
    elems: seq[tuple[mvar: string, repeat: bool, info: NimNode]]

  NonTerminalDef = object
    ## Pre-processed non-terminal definition.
    name: NimNode
    sub: seq[NimNode]
    add: seq[NimNode]

type
  # Internal types used for the macro. To allow for strong static typing, the
  # framework needs access to some
  PForm[I: static int] = object

  PChoice[A, B] = object
    ## Predicate: T is `A` or `B`.

  PArray[A] = object
    ## Predicate: T is array-like with element `A`.

  Static[V: static int] = distinct int
    ## Carrier for a compile-time known integer value.

  SForm = object
    ## Semantic-focused representation of a syntax form, optimized for
    ## macro processing.
    name: string
    ntag: int
      ## the node tag identifying the form in an AST
    elems: seq[tuple[typ: int, repeat: bool]]

  LangType = object
    ## Terminals and non-terminals modeled as types.
    name: string
    mvar: string
      ## name of a meta-variable that is used to range over the type
    case terminal: bool
    of true:
      ntag: int
        ## the tag with which a node storing the terminal value is identified
    of false:
      sub: seq[int]
        ## the types part of the union
      forms: seq[int]
        ## all production forms of the non-terminal

  LangInfo = object
    ## Representation of a language definition that stores the information in
    ## a way that make it easier to work with for the DSL macros.
    # important: for compilation speed, the AST representation of the data
    # should be as short and concise as possible
    types: seq[LangType]
    map: Table[string, int]
      ## maps type and meta-var names to the corresponding type
    forms: seq[SForm]

const
  RefTag = 128'u8
    ## the node used internally for indirections
  FirstTerminalTag = RefTag + 1
    ## the start of the terminals' tag space

template findIt[T](s: seq[T], predicate: untyped): untyped =
  ## Version of ``find`` that allows providing an inline predicate,
  ## evaluated for every checked item.
  var r = -1
  block:
    for i, it {.inject.} in s.pairs:
      if predicate:
        r = i
  r

macro dot(e, fname: untyped): untyped =
  ## ``dot(x, "abc")`` -> ``x.abc``.
  macro dotAux(fname: static string, e: untyped): untyped =
    newDotExpr(e, ident(fname))

  newCall(bindSym"dotAux", fname, e)

template matches*[T, U](x: T, _: typedesc[U]): bool =
  ## Implements type-based pattern matching, used by the nanopass macros.
  when U is PArray:
    when T is seq:
      matches(default(typeof(x[0])), typeof(U.A))
    else:
      false
  elif U is PChoice:
    # why not just use `or`? Because that would unnecessarily expand the
    # second `matches` invocation when the case first invocation was sucessful
    when matches(x, typeof(U.A)):
      true
    else:
      matches(x, typeof(U.B))
  elif U is Metavar:
    when x is U:
      true
    else:
      matches(x, dot(U.L.meta.nt, U.N))
  else:
    x is U

proc lookup[E; M: tuple](): auto {.compileTime.} =
  var x: M
  for it in fields(x):
    when E is typeof(it[0]):
      return it[1]

template isAtom*(x: uint8): bool =
  ## The predicate required for using an uint8 as a ``PackedTree`` tag.
  x >= RefTag

proc `$`(x: Form): string =
  result = x.tag
  result.add "("
  for i, it in x.elems.pairs:
    if i > 0:
      result.add ", "
    result.add it.typ
  result.add ")"

proc `$`*(x: LangDef): string =
  for it in x.forms.items:
    result.add $it
    result.add "\n"

proc `==`(x, y: Elem): bool =
  x.typ == y.typ and x.repeat == y.repeat

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

proc parseForm(n: NimNode): ParsedForm =
  ## Parses a form in the context of a language definition. No semantic checks
  ## take place.
  n[0].expectKind nnkIdent
  result.name = n[0].strVal
  for i in 1..<n.len:
    var repeat = false
    var it = n[i]
    if it.kind == nnkPrefix and it[0].eqIdent("..."):
      repeat = true
      it = it[1]

    it.expectKind nnkIdent
    result.elems.add (it.strVal, repeat, it)

proc addForm(def: var LangDef, form: Form): int =
  def.forms.add form
  result = def.forms.high

proc computeNodeTags(def: var LangDef) =
  ## Assigns node tags to forms and terminals.
  var next = 0
  for it in def.forms.items:
    next = max(it.id + 1, next)
  # ^^ while simple, this does waste ID space

  for it in def.forms.mitems:
    # TODO: report an error when the ID overflows the allowed range
    if it.id == -1:
      it.id = next
      inc next

  next = int FirstTerminalTag
  for it in def.terminals.values:
    next = max(it.tag + 1, next)

  for it in def.terminals.mvalues:
    if it.tag == -1:
      it.tag = next
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
    if name notin base.terminals or base.terminals[name].typ != typ:
      error("terminal does not exist in the base language", it)
    base.terminals.del(name)

  result.terminals = base.terminals

  var vars: Table[string, string]
  for it in result.terminals.keys:
    vars[it] = it

  proc removeProd(def: var LangDef, n: NimNode, to: string) =
    proc find(def: LangDef, nt: NonTerminal, f: ParsedForm): int =
      for i, it in nt.forms.pairs:
        if def.forms[it.semantic].tag == f.name and
           it.vars.len == f.elems.len:
          block search:
            # compare the elements:
            for j in 0..<f.elems.len:
              if f.elems[j].repeat != def.forms[it.semantic].elems[j].repeat or
                 f.elems[j].mvar != it.vars[j]:
                break search

            return i
      result = -1

    case n.kind
    of nnkCall:
      let idx = def.find(def.nterminals[to], parseForm(n))
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

  proc checkForm(def: LangDef, vars: Table[string, string], form: OrigForm,
                 info: NimNode) =
    for i, it in form.vars.pairs:
      if it in vars:
        if vars[it] != def.forms[form.semantic].elems[i].typ:
          error(fmt"cannot inherit '{form}'; '{it}' changed its meaning",
                info)
      else:
        error(fmt"cannot inherit '{form}'; '{it}' was removed", info)

  # after all that setup, the productions can finally be inherited:
  for name, it in base.nterminals.pairs:
    var res = it
    # inherit the forms and patch references:
    for f in res.forms.mitems:
      # make sure the forms are still valid after the previous removals/renames
      checkForm(base, vars, f, info)
      var idx = result.forms.find(base.forms[f.semantic])
      if idx == -1:
        idx = result.addForm(base.forms[f.semantic])
      f.semantic = idx

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
    # the node tag is filled in later
    result.terminals[name] = (typ, -1)
    vars[name] = name

  proc addProd(def: var LangDef, n: NimNode, to: string) =
    proc addForm(def: var LangDef, p: ParsedForm): OrigForm =
      var form = Form(tag: p.name, id: -1) # the ID is computed later

      for i, (name, repeat, info) in p.elems.pairs:
        if name notin vars:
          error(fmt"no meta-var with name '{name}' exists", info)

        form.elems.add Elem(repeat: repeat, typ: vars[name])
        result.vars.add name

      var index = def.forms.find(form)
      if index == -1:
        index = def.addForm(form)
      result.semantic = index

    case n.kind
    of nnkCall:
      let got = def.addForm(parseForm(n))
      if def.nterminals[to].forms.findIt(it.semantic == got.semantic) != -1:
        error(fmt"production is already part of '{to}'", n)
      def.nterminals[to].forms.add got
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

  computeNodeTags(result)
  # TODO: properly set the entry non-terminal
  result.entry = "module"

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

  var body = body
  if body.kind != nnkStmtList:
    body = newStmtList(body)

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

proc buildLangInfo(def: LangDef): LangInfo =
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

proc defineLanguageImpl(name, base, body: NimNode): NimNode =
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

macro defineLanguage*(name, body: untyped) =
  ## Creates a language definition and binds it to a const symbol with the
  ## given name.
  defineLanguageImpl(name, nil, body)

macro defineLanguage*(name, base, body: untyped) =
  ## Creates a language definition, extending `base`, and binds it to a const
  ## symbol with the given name. Extension doesn't imply a direction in this
  ## context.
  defineLanguageImpl(name, base, body)

# -------- macro helpers -------

proc copyLineInfoForTree(n, info: NimNode) =
  copyLineInfo(n, info)
  for i in 0..<n.len:
    copyLineInfoForTree(n[i], info)

proc makeError(msg: string, info: NimNode): NimNode =
  ## Creates an error statement reporting `msg` at the given source location.
  let it = nnkExprColonExpr.newTree(ident"error", newStrLitNode(msg))
  result = nnkPragma.newTree(it)
  copyLineInfoForTree(result, info)

proc finish*(ast: PackedTree[uint8], n: NodeIndex): PackedTree[uint8] =
  ## Returns `ast` with all indirections resolved.
  # TODO: don't export the procedure
  template src: untyped = ast.nodes
  template dst: untyped = result.nodes
  const size = sizeof(TreeNode[uint8])

  # search for runs of contiguous nodes. When encountering an indirection,
  # copy the run and move the source cursor to the indirection's
  # target; repeat.
  var stack = @[(uint32(n), uint32(n))]
  while stack.len > 0:
    block outer:
      var (i, last) = stack[^1]
      let prev = i
      while i <= last:
        if src[i].kind < RefTag:
          last += src[i].val
        elif src[i].kind == RefTag:
          if i > prev:
            # copy everything we got so far
            let pos = dst.len
            dst.setLen(pos + int(i - prev))
            copyMem(addr dst[pos], addr src[prev], int(i - prev) * size)

          stack[^1] = (i + 1, last)
          let next = src[i].val
          stack.add (next, next)
          break outer

        inc i

      if i > prev:
        # copy the rest
        let pos = dst.len
        dst.setLen(pos + int(i - prev))
        copyMem(addr dst[pos], addr src[prev], int(i - prev) * size)

      stack.shrink(stack.len - 1)

# ------- build macro -------

proc append[L, U](to: var PackedTree[uint8], x: Value[U]) =
  to.nodes.add TreeNode[uint8](kind: typeof(lookup[U, L.meta.term_map]()).V)

proc append[L](to: var PackedTree[uint8], x: Metavar) =
  to.nodes.add TreeNode[uint8](kind: RefTag, val: uint32(x.index))

proc append(to: var PackedTree[uint8], i: var int, x: Metavar) =
  to.nodes[i] = TreeNode[uint8](kind: RefTag, val: uint32(x.index))
  inc i

proc append[L](to: var PackedTree[uint8], x: openArray) =
  for it in x.items:
    append[L](to, it)

# helpers for `buildImpl`
template len(x: Value): int = 1
template len(x: Metavar): int = 1

macro buildImpl(to: var PackedTree[uint8], lang: static LangInfo,
                typ: typedesc[Metavar], e: untyped): untyped =
  ## Emits a tree construction for the AST described by `e`, with the syntax
  ## from `lang`.
  proc cons(lang: LangInfo, n, test, body: NimNode): NimNode {.closure.}

  proc elem(lang: LangInfo, n, test, body: NimNode): NimNode =
    ## Processor for element syntax.
    case n.kind
    of nnkCall:
      result = cons(lang, n, test, body)
    of nnkBracket:
      result = nnkBracket.newTree()
      for it in n.items:
        result.add elem(lang, it, test, body)
    of nnkIdent, nnkSym, nnkAccQuoted:
      # some hoisted expression
      result = n
      body.add genAst(typ, to, n) do:
        append[typ.L](to, n)
    else:
      error("unexpected syntax", n)

  proc form(lang: LangInfo, n, test, body: NimNode): NimNode =
    ## Processor for a tree construction.
    let tag = n[0].strVal
    var elems: seq[NimNode]
    var temp = newStmtList()
    for i in 1..<n.len:
      elems.add elem(lang, n[i], test, temp)

    proc appendCheck(to: var NimNode, e, pat: NimNode) =
      let sym = bindSym"matches"
      to = quote do:
        `to` and `sym`(`e`, `pat`)

    proc access(t: LangType): NimNode =
      newDotExpr(newDotExpr(typ, ident"L"), ident(t.mvar))

    # multiple forms may share the same name. A when statement is used to
    # figure out the one to use at compile time (overload resolution)
    let whenStmt = nnkWhenStmt.newTree()
    for form in lang.forms.items:
      if form.name == tag and form.elems.len == elems.len:
        # the condition is a chain of checks; the body is a value whose type
        # stores the form's ID
        var cond = ident"true"
        for i, e in form.elems.pairs:
          let inp = elems[i]
          if e.repeat:
            let acc = access(lang.types[e.typ])
            if inp.kind == nnkBracket:
              # every item in the bracket must match the repetition's type
              for s in inp.items:
                cond.appendCheck(s, acc)
            else:
              # the operand msut be an array-like
              cond.appendCheck(inp, nnkBracketExpr.newTree(bindSym"PArray", acc))
          else:
            if inp.kind == nnkBracket:
              cond = ident"false" # type mismatch
              break
            else:
              cond.appendCheck(inp, access(lang.types[e.typ]))

        whenStmt.add nnkElifBranch.newTree(cond,
          nnkObjConstr.newTree(
            nnkBracketExpr.newTree(bindSym"PForm", newIntLitNode(form.ntag))))

    if whenStmt.len == 0:
      test.add makeError(fmt"no form with arity {elems.len} exists", n)
      result = ident"true"
    else:
      whenStmt.add nnkElse.newTree(
        makeError("no form with the given shape exists", n))

      let res = genSym("form")
      test.add newLetStmt(res, whenStmt)

      var len = newIntLitNode(0)
      for it in elems.items:
        let t =
          if it.kind == nnkPar: newIntLitNode(1)
          elif it.kind == nnkBracket: newIntLitNode(it.len)
          else: newCall(bindSym("len", brOpen), it)

        len = nnkInfix.newTree(ident"+", len, t)
      body.add quote do:
        `to`.nodes.add TreeNode[uint8](kind: typeof(`res`).I.uint8,
                                       val: uint32(`len`))
      body.add temp
      # a par distinguishes an inline constructed tree from some embedded value
      result = nnkPar.newTree(res)

  proc cons(lang: LangInfo, n, test, body: NimNode): NimNode =
    ## Processor for a ``X(...)`` expression, which may either be a terminal
    ## construction or inline tree construction.
    n[0].expectKind nnkIdent
    let name = n[0].strVal
    if name in lang.map:
      # can only be a terminal
      n.expectLen 2
      let valueType = ident(lang.types[lang.map[name]].name)
      let sym = genSym()
      discard n[1]
      # TODO: add the value to the environment
      test.add quote do:
        let `sym` = Value[`valueType`]()
      body.add genAst(typ, to, sym) do:
        append[typ.L](to, sym)
      nnkPar.newTree(sym)
    else:
      form(lang, n, test, body)

  var constr = newStmtList() ## the tree construction
  result = newStmtList()
  let got = elem(lang, e, result, constr)
  if constr.len == 0:
    result.add genAst(got, typ, to) do:
      when not matches(got, typ):
        {.error: $typeof(got) & " is not a production of '" & typ.N & "'".}
      when got is Metavar: # is it just a type conversion?
        typ(index: got.index)
      else:
        append[typ.L](to, got)
        typ(index: NodeIndex(to.nodes.high))
  else:
    result.add genAst(got, typ, to, constr) do:
      when not matches(got, typ):
        {.error: "form is not a production of '" & typ.N & "'".}
      let tmp = to.nodes.len
      constr
      typ(index: NodeIndex(tmp))

  # wrap in a scope such that temporaries don't spill over
  result = nnkBlockExpr.newTree(newEmptyNode(), result)

macro buildFirstPass(to, mv, e: untyped): untyped =
  ## Implements the first half of the ``build`` macro. Hoists all unquotes out
  ## of `e`. For example:
  ##   build ..., If(^x, ^y, Call(^z))
  ## becomes:
  ##   let tmp_1 = x
  ##   let tmp_2 = y
  ##   let tmp_3 = z
  ##   build ..., If(tmp_1, tmp_2, Call(tmp_3))
  result = newStmtList()
  proc hoist(n: NimNode, list: NimNode): NimNode =
    case n.kind
    of nnkCall:
      n.expectMinLen 1
      n[0].expectKind nnkIdent
      result = n
      for i in 1..<n.len:
        result[i] = hoist(n[i], list)
    of nnkBracket:
      result = n
      for i in 0..<n.len:
        result[i] = hoist(n[i], list)
    of nnkPrefix:
      if n[0].strVal == "^":
        # an unquote
        let tmp = genSym()
        list.add newLetStmt(tmp, n[1])
        result = tmp
      else:
        error("unexpected syntax", n)
    of nnkIdent, nnkSym, nnkAccQuoted:
      # auto-unquote as it cannot be anything part of the construction
      let tmp = genSym()
      list.add newLetStmt(tmp, n)
      result = tmp
    else:
      error("unexpected syntax", n)

  let e = hoist(e, result)
  let impl = bindSym"buildImpl"
  result.add quote do:
    `impl`(`to`, idef(`mv`.L), `mv`, `e`)

template build*(ast: var PackedTree[uint8], mv: typedesc[Metavar],
                e: untyped): untyped =
  ## Creates the AST described by `e`, with the syntax from `lang`. Returns a
  ## `Metavar` pointing to the created AST fragment.
  buildFirstPass(ast, mv, e)

template embed*(lang: typedesc, arg: untyped): untyped =
  # TODO: implement, and don't export
  let tmp = arg
  Value[typeof(tmp)]()

# -------- pass macros --------

macro transformOutImpl(lang: static LangDef, name, def: untyped) =
  ## Implements the transformation for processors in an *->language pass.
  if def.kind notin {nnkProcDef, nnkFuncDef}:
    error(".transform must be applied to procedure definition", def)

  if def.body.kind == nnkEmpty:
    # a forward declaration, bail
    return def

  let to = ident"out.ast"
  let ret = def.params[0]
  def.body = newStmtList(def.body)
  def.body.insert 0, quote do:
    # inject a build overload that implicitly uses the output language
    template build(body: untyped): untyped {.used.} =
      build(`to`, `ret`, body)

  result = def

macro transform(src, dst: static LangDef, nterm: static string,
                form: static int, n: untyped): untyped =
  ## Generates the transformation from the given source language form
  ## (belonging to non-terminal `nterm`) to a target language form with
  ## compatible syntax.
  # find a target language form that's a production of the non-terminal and has
  # the same shape
  # TODO: only require the same name and number of elements, using -> to fit
  #       the rest. **Edit:** really? That can easily lead to non-obvious
  #       behaviour
  var target = -1
  for it in dst.nterminals[nterm].forms.items:
    if dst.forms[it.semantic] == src.forms[form]:
      target = it.semantic
      break
  if target == -1:
    return makeError(fmt"cannot generate transformer for '{src.forms[form]}'", n)

  # important: the generated code being efficient is of major importance! Most
  # transformations will be auto-generated, and they should thus be as fast as
  # possible
  # TODO: if none of the child nodes require a processor call, memcopy the
  #       whole sub-tree
  # TODO: (bigger refactor) pass the cursor to the transformers as a var
  #       parameter, which would eliminate unnecessary tree seeking when
  #       there's many calls to fully auto-generated non-terminal processors

  let inAst = ident"in.ast"
  let to = ident"out.ast"
  let id = dst.forms[target].id.uint8
  result = newStmtList()
  # add the root node:
  let body = quote do:
    var tmp {.used.} = `inAst`.child(`n`, 0)
    let root = `to`.nodes.len.NodeIndex
    var i = `to`.nodes.len
    # the node sequence needs to be contiguous, so it's allocated upfront
    `to`.nodes.setLen(i + `inAst`.len(`n`) + 1)
    `to`.nodes[i] = TreeNode[uint8](kind: `id`, val: `inAst`[`n`].val)
    inc i

  # call the transformers and emit the nodes in one go:
  for i, it in src.forms[form].elems.pairs:
    let fromTerminal = it.typ in src.terminals
    let toTerminal = it.typ in dst.terminals
    if fromTerminal != toTerminal or
       (toTerminal and src.terminals[it.typ].typ != src.terminals[it.typ].typ):
      body.add makeError(fmt"cannot generate transformer for {src.forms[form]}", n)
      break

    let call =
      if fromTerminal:
        if src.terminals[it.typ].tag == dst.terminals[it.typ].tag:
          # just copy the node
          quote do:
            `to`.nodes[i] = `inAst`[tmp]
            inc i
        else:
          # repack with the new tag
          let tag = dst.terminals[it.typ].tag
          quote do:
            `to`.nodes[i] = TreeNode[uint8](kind: `tag`, val: `inAst`[tmp].val)
            inc i
      else:
        let append = bindSym"append"
        let op = ident"->"
        let s = newStrLitNode(it.typ)
        let d = newStrLitNode(dst.forms[target].elems[i].typ)
        quote do:
          `append`(`to`, i,
            `op`(Metavar[src, `s`](index: tmp), Metavar[dst, `d`]))

    if it.repeat:
      let bias = src.forms[form].elems.len - 1
      body.add quote do:
        for _ in 0..<(`inAst`.len(`n`) - `bias`):
          `call`
          tmp = `inAst`.next(tmp)
    else:
      body.add quote do:
        `call`
        tmp = `inAst`.next(tmp)

  result.add body
  # the callsite takes care of fitting the index to the right type
  result.add ident"root"

proc ntags(lang: LangInfo, typ: LangType): seq[int] =
  ## Returns a list with all possible node tags productions of `typ` can have.
  for it in typ.forms.items:
    result.add lang.forms[it].ntag

  for it in typ.sub.items:
    if lang.types[it].terminal:
      result.add lang.types[it].ntag
    else:
      result.add ntags(lang, lang.types[it])

proc matchImpl(lang: LangInfo, src: int, ast, sel, rules: NimNode
              ): (seq[NimNode], IntSet) =
  ## Implements the core of the `match` macro:
  ## 1. makes sure the syntax is correct
  ## 2. makes sure the used patterns are unique
  ## 3. generates a sequence of transformed 'of' branches, plus a set storing
  ##    the used forms' tags
  var used: IntSet
    ## covered form productions (identified by ntag)

  # should nested matching (e.g., ``A(x, B(y))``) be desired, `matchImpl`
  # should be factored into two macros macros applied sequentially:
  # 1. the first macro does type checking, producing a type form
  # 2. the second macro translates the typed form into case/if statements
  # combining both steps into one is simple enough when there are no nested
  # patterns, but not otherwise

  proc parseVar(n: NimNode): (string, string) =
    n.expectKind nnkIdent
    let name = n.strVal
    var e = name.high
    # to get the name of the var, trim trailing numbers and a single underscore
    while e >= 0 and name[e] in {'0'..'9'}:
      dec e

    if e >= 0 and name[e] == '_':
      dec e

    result[0] = name[0..e]
    result[1] = name

  proc processIdentPattern(lang: LangInfo, n: NimNode): (NimNode, NimNode) =
    n.expectKind nnkIdent
    let (v, nameStr) = parseVar(n)
    if v notin lang.map:
      error(fmt"no meta-variable with name '{v}'", n)
    let id = lang.map[v]
    if id notin lang.types[src].sub:
      error(fmt"'{v}' is not an immediate production of '{lang.types[src].name}'", n)

    var check, binds: NimNode
    let name = ident(nameStr)
    if lang.types[id].terminal:
      let typ = ident(lang.types[id].name)
      let tag = lang.types[id].ntag
      used.incl(tag)
      # let the compiler report an error for duplicate case labels
      check = newIntLitNode(tag)
      copyLineInfo(check, n)
      binds = newLetStmt(name, quote do: Value[`typ`](index: `ast`[`sel`].val))
    else:
      # the pattern binds a non-terminal
      let typ = ident(v)
      check = nnkCurly.newTree()
      let tags = ntags(lang, lang.types[id])
      for tag in tags.items:
        check.add nnkConv.newTree(ident"uint8", newIntLitNode(tag))
      # mark the first tag as used, to signal that the non-terminal is handled
      used.incl(tags[0])

      copyLineInfoForTree(check, n)
      binds = newLetStmt(name, quote do: src.`typ`(index: `sel`))

    result = (check, binds)

  proc processPattern(lang: LangInfo, n: NimNode): (NimNode, NimNode) =
    case n.kind
    of nnkCall:
      n[0].expectKind nnkIdent
      # parse the pattern:
      var elems = newSeq[tuple[src, dst, name: string]](n.len - 1)
      for i in 1..<n.len:
        case n[i].kind
        of nnkIdent:
          let (v, name) = parseVar(n[i])
          if v notin lang.map or lang.types[lang.map[v]].name == v:
            error(fmt"no metavar named {v}", n[i])
          elems[i - 1] = (v, "", name)
        of nnkBracket:
          n[i].expectLen 1
          let (v, name) = parseVar(n[i][0])
          # cannot check whether the metavar exists. If it doesn't, the
          # compiler will complain with a not-so-helpful error
          elems[i - 1] = ("", v, name)
        else:
          error("unexpected syntax", n)

      # TODO: enforce during language constructions that there are no two
      #       productions that use the same ntag
      var idx = -1
      block search:
        # find a production that matches the pattern:
        for it in lang.types[src].forms.items:
          block form:
            if lang.forms[it].elems.len == elems.len and
               lang.forms[it].name == n[0].strVal:
              for j in 0..<elems.len:
                if elems[j].src != "" and
                   lang.forms[it].elems[j].typ != lang.map[elems[j].src]:
                  # different types, no match
                  break form
                # the `[...]` syntax (i.e., no source type) matches everything
              # found a matching form
              idx = it
              break search
        error(fmt"no production of '{src}' matches the pattern", n)

      let tag = lang.forms[idx].ntag
      let check = newIntLitNode(tag)
      copyLineInfo(check, n)

      # let the compiler report a duplicate case label error
      used.incl(tag)

      if lang.forms[idx].elems.len == 0:
        # form with no elements; nothing to bind
        return (check, newStmtList())

      var binds = newStmtList()
      var cursor = genSym("c")
      binds.add newVarStmt(cursor, quote do: `ast`.child(`sel`, 0))

      # create the check and the bindings
      for i, it in lang.forms[idx].elems.pairs:
        let p = n[i + 1] ## the pattern expression
        let origin = newDotExpr(ident"src", ident(lang.types[it.typ].mvar))
        let target = newDotExpr(ident"dst"):
          if elems[i].dst.len > 0: ident(elems[i].dst)
          else:                    ident(lang.types[it.typ].mvar)
        if it.repeat:
          let bias = lang.forms[idx].elems.len - 1
          if p.kind == nnkIdent:
            # just bind a child slice to the identifier
            binds.add newLetStmt(p, quote do:
              slice[`origin`](`cursor`, uint32(`ast`.len(`sel`) - `bias`)))
            binds.add quote do:
              for _ in 0..<`ast`.len(`sel`)-`bias`:
                `cursor` = `ast`.next(`cursor`)
          else:
            # run the selected transformer on all relevant child nodes and
            # store the result in a seq
            let tmp = genSym()
            binds.add newVarStmt(tmp,
              quote do: newSeq[`target`](`ast`.len(`sel`)-`bias`))
            let callee = ident"->"
            binds.add quote do:
              for i in 0..<`ast`.len(`sel`)-`bias`:
                `tmp`[i] = `callee`(`origin`(index: `cursor`), `target`)
                `cursor` = `ast`.next(`cursor`)
            binds.add newLetStmt(p[0], tmp)
        else:
          # simple case: a single node
          if p.kind == nnkIdent:
            if lang.types[it.typ].terminal:
              binds.add newLetStmt(p, quote do: `origin`(index: `ast`[`cursor`].val))
            else:
              binds.add newLetStmt(p, quote do: `origin`(index: `cursor`))
          else:
            if lang.types[it.typ].terminal:
              binds.add makeError("cannot invoke auto-procesor for terminal", p)
            else:
              binds.add newLetStmt(p[0],
                newCall(ident"->",
                  nnkObjConstr.newTree(origin,
                    nnkExprColonExpr.newTree(ident"index", cursor)),
                  target))
          binds.add quote do:
            `cursor` = `ast`.next(`cursor`)
      result = (check, binds)
    of nnkIdent:
      # must be a terminal/non-terminal meta-var
      result = processIdentPattern(lang, n)
    else:
      error("unexpected syntax", n)

  var branches: seq[NimNode]
  for it in rules.items:
    case it.kind
    of nnkOfBranch:
      it.expectLen 2
      let (check, binds) = processPattern(lang, it[0])
      branches.add nnkOfBranch.newTree(check, newStmtList(binds, it[1]))
    of nnkElse:
      # as a guard against malformed run-time inputs, use an 'of' instead
      # of an 'else' branch
      var ofb = nnkOfBranch.newTree()
      # add all remaining forms:
      for it in lang.types[src].forms.items:
        if not containsOrIncl(used, lang.forms[it].ntag):
          ofb.add newIntLitNode(lang.forms[it].ntag)
      # also include the tags for sub non-terminals and terminals:
      for it in lang.types[src].sub.items:
        if lang.types[it].terminal:
          if not containsOrIncl(used, lang.types[it].ntag):
            ofb.add newIntLitNode(lang.types[it].ntag)
        else:
          let tags = ntags(lang, lang.types[it])
          if not containsOrIncl(used, tags[0]):
            for tag in tags.items:
              ofb.add newIntLitNode(tag)

      if ofb.len == 0:
        # all forms are handled already. Add an 'else' branch before the
        # programmer-provided one so that the compiler can report an
        # "unreachable" warning
        branches.add nnkElse.newTree(newCall(ident"unreachable"))
        branches.add it
      else:
        copyLineInfo(ofb, it)
        ofb.add it[0]
        branches.add ofb
    else:
      error("expected 'of' or 'else'", it)

  result = (branches, used)

macro processorMatchImpl(lang: static LangInfo, src: static string,
                         sel: untyped, rules: varargs[untyped]): untyped =
  ## Implements the transformation/expansion of a language->language
  ## processor's trailing case statement/expression.
  let id = lang.map[src]
  var (branches, used) = matchImpl(lang, id, ident"in.ast", sel, rules)

  template nt: untyped = lang.types[id]
  let sym = bindSym"transform"
  # auto-generate the transformers for the forms not manually provided:
  for it in nt.forms.items:
    let id = lang.forms[it].ntag
    if not containsOrIncl(used, id):
      branches.add nnkOfBranch.newTree(
        newIntLitNode(id),
        (quote do:
          Metavar[dst, `src`](index: `sym`(def(src), def(dst), `src`, `it`, `sel`))))

  # auto-generate the branches for missing production terminals and
  # non-terminals:
  for it in nt.sub.items:
    if lang.types[it].terminal:
      let id = lang.types[it].ntag
      if id notin used:
        let to = ident"out.ast"
        let input = ident"in.ast"
        branches.add nnkOfBranch.newTree(
          newIntLitNode(id),
          (quote do:
            # TODO: use the tag of the destination language
            `to`.nodes.add:
              TreeNode[uint8](kind: uint8(`id`), val: `input`[`sel`].val)
            Metavar[dst, `src`](index: NodeIndex(`to`.nodes.high))))
    else:
      # if the first form's tag is used, so is the non-terminal itself
      if lang.forms[lang.types[it].forms[0]].ntag notin used:
        # TODO: consider inlining the transformer if it's auto-generated.
        #       More code to emit, but also a little less work at run-time
        let branch = nnkOfBranch.newTree()
        for tag in ntags(lang, lang.types[it]).items:
          branch.add newIntLitNode(tag)
        let name = ident(lang.types[it].mvar)
        let callee = ident"->"
        # dispatch to the processor and convert to the expected type
        branch.add quote do:
          Metavar[dst, `src`](
            index: `callee`(src.`name`(index: `sel`), dst.`name`).index)
        branches.add branch

  let input = ident"in.ast"
  result = nnkCaseStmt.newTree(quote do: `input`[`sel`].kind)
  result.add branches
  if branches[^1].kind != nnkElse:
    # the selector is a uint8 and thus the case cannot be exhaustive
    result.add nnkElse.newTree(newCall(ident"unreachable"))

macro matchImpl(lang: static LangInfo, nterm: static string,
                ast: PackedTree[uint8], sel: NodeIndex, info: untyped,
                rules: varargs[untyped]): untyped =
  ## The internal implementation `match` dispatches to.
  let (branches, used) = matchImpl(lang, lang.map[nterm], ast, sel, rules)
  result = nnkCaseStmt.newTree(quote do: `ast`[`sel`].kind)
  copyLineInfoForTree(result, info)
  result.add branches
  # add a default handler when all possible productions are covered
  var allCovered = true
  for it in lang.types[lang.map[nterm]].sub.items:
    if lang.types[it].terminal:
      if lang.types[it].ntag notin used:
        allCovered = false
        break
    elif lang.forms[lang.types[it].forms[0]].ntag notin used:
      allCovered = false
      break

  if allCovered:
    result.add nnkElse.newTree(newCall(ident"unreachable"))

template match*(ast: PackedTree[uint8], nt: Metavar,
                branches: varargs[untyped]): untyped =
  ## Provides a convenient way to destructure an AST. Meant to be used as
  ## follows:
  ##
  ## .. code-block:: nim
  ##
  ##   match ast, n:
  ##   of ...: discard
  ##   of ...: discard
  ##   else:   discard
  bind matchImpl
  let idx = nt.index
  matchImpl(idef(typeof(nt).L), typeof(nt).N, ast, idx, nt, branches)

macro genProcessor*(index, nterm: untyped): untyped =
  ## Generates the body for a non-terminal processor.
  # simply emit an empty processorMatchImpl invocation. All branches will be
  # auto-generated
  # TODO: if none of the productions require a (direct or indirect) call to a
  #       custom processor, the source and target productions match, and the
  #       used tags map to the same ID in the source and target language, use a
  #       memcopy
  let sym = bindSym"processorMatchImpl"
  result = quote do:
    `sym`(idef(src), `nterm`, `index`)

proc hasPragma(def: NimNode, name: string): bool =
  if def.pragma.kind == nnkPragma:
    for it in def.pragma.items:
      if it.eqIdent(name):
        return true

macro genAdapter[T1, T2; A, B: static string](
    src: typedesc[Metavar[T1, A]], dst: typedesc[Metavar[T2, B]],
    orig: untyped) =
  # note: the macro signature is very specific because it acts as the type
  # checking for programmer-provided processor signatures
  let name = ident("->")
  copyLineInfo(name, orig)
  result = quote do:
    template `name`(n: `src`, _: typedesc[`dst`]): `dst` =
      {.line.}: `orig`(n)

macro transformInOutImpl(lang: static LangDef, name, def: untyped) =
  ## Implements the transformation for language->language pass processors.
  let name = name
  if def.kind notin {nnkProcDef, nnkFuncDef}:
    error(".transform must be applied to procedure definition", def)

  if def.params[0].kind == nnkEmpty:
    error("a return type is required for a transfomer", def.name)

  if def.body.kind == nnkEmpty:
    # a forward declaration. Append the additional adapter procedure
    return newStmtList(def,
      newCall(bindSym"genAdapter",
        copyNimTree(def.params[1][^2]),
        copyNimTree(def.params[0]),
        copyNimNode(def.name)))

  proc transformCase(n: NimNode): NimNode =
    result = genAst(arg=n[0]):
      processorMatchImpl(idef(src), typeof(arg).N, arg.index)
    for i in 1..<n.len:
      result.add n[i]

  var inner = def.body
  if inner.kind == nnkCaseStmt:
    inner = transformCase(inner)
  elif inner.kind == nnkStmtList:
    if inner[^1].kind == nnkCaseStmt:
      inner[^1] = transformCase(inner[^1])
    else:
      error("trailing statement/expression must be 'case'", inner[^1])
  else:
    error("trailing statement/expression must be 'case'", inner)

  let to = ident"out.ast"
  let ret = def.params[0]
  def.body = newStmtList(def.body)
  def.body.insert 0, quote do:
    # inject a build macro overload that implicitly uses the
    # target non-terminal
    template build(body: untyped): untyped {.used.} =
      build(`to`, `ret`, body)

  result = def

macro transformInImpl(lang: static LangDef, name, def: untyped) =
  ## Implements the processing for transformers part of an input pass.
  result = def

macro generatedImpl(def: untyped) =
  ## Implements the `.generated` pragma for language->language passes.
  if def.body.kind != nnkEmpty:
    error(".generated must be applied to forward declaration", def)

  def.body = newCall(ident"->", def.params[1][0], copyNimTree(def.params[0]))
  result = def

proc assemblePass(src, dst, def, call: NimNode): NimNode =
  ## Assembles the final procedure definition for a pass. `def` is the original
  ## proc definition, `call` the call to the pass' implementation.
  let input = ident"in.ast"
  let output = ident"out.ast"
  let hasIn = src != nil
  let hasOut = dst != nil

  var body = newStmtList()
  let (transformImpl, name) =
    if hasIn and hasOut:
      (bindSym"transformInOutImpl", dst)
    elif hasIn:
      (bindSym"transformInImpl", src)
    elif hasOut:
      (bindSym"transformOutImpl", dst)
    else:
      unreachable()

  body.add quote do:
    template transform(p: untyped) {.used.} =
      `transformImpl`(def(`name`), `name`, p)

  if hasIn and hasOut:
    let impl = bindSym"generatedImpl"
    body.add quote do:
      template generated(p: untyped) {.used.} = `impl`(p)

  # alias the source and destination language with known names:
  if hasIn:
    body.add quote do:
      template src: untyped {.used.} = `src`
  if hasOut:
    body.add quote do:
      template dst: untyped {.used.} = `dst`

  if hasIn:
    let inj = ident"[]"
    body.add quote do:
      template match(sel: Metavar, branches: varargs[untyped]): untyped {.used.} =
        match(`input`, sel, branches)

      template `inj`(x: ChildSlice, i: int): untyped {.used.} =
        `input`[x, i]

      template val[T](v: nanopass.Value[T]): T {.used.} =
        # TODO: look up the value of the terminal. Also, return a `lent T`
        default(typeof(T))

  if hasOut:
    body.add quote do:
      template terminal(x: untyped): untyped {.used.} =
        embed(`name`, x)
      template build(n: typedesc[Metavar], body: untyped): untyped {.used.} =
        build(`output`, n, body)

  if hasIn:
    # shadow the input tree with a cursor to prevent a costly copy when
    # it's captured by the closure
    body.add quote do:
      let `input` {.cursor.} = `input`.tree
  if hasOut:
    body.add quote do:
      var `output`: PackedTree[uint8]
      let index = `call`.index
      # turn the AST with indirections into one without
      result = Ast[dst](tree: finish(`output`, index))
  else:
    body.add quote do:
      result = `call`

  def.body = body
  # patch the signature:
  if hasIn:
    def.params[1][^2] = ident"NodeIndex"
    def.params.insert(1, newIdentDefs(ident"in.ast", quote do: Ast[`src`]))
  if hasOut:
    def.params[0] = nnkBracketExpr.newTree(ident"Ast", dst)

  result = def

macro passImpl(src, dst, srcnterm, dstnterm: typedesc, def: untyped) =
  # create a forward declaration for each transformer:
  var preamble = newStmtList()
  var i = 0
  while i < def.body.len:
    let it = def.body[i]
    # not ideal, as it breaks some custom macro/template pragmas, but without
    # resorting to typed macros, there's no other way to do this transform
    if it.kind == nnkProcDef and it.hasPragma("transform"):
      if it.body.kind == nnkEmpty:
        # remove the user-defined forward declaration
        def.body.del(i)
        dec i # undo the following `inc`
      else:
        let backup = it.body
        it.body = newEmptyNode()
        preamble.add copyNimTree(it)
        it.body = backup
    inc i

  # add the generic processor procedure, which all processor invocations
  # for processors not supplied by the programmer will end up using
  let name = ident"->"
  preamble.add quote do:
    # note: the signature is overly broad, so that overload resolution
    # prefers the more specific adapters created for the programmer-provided
    # processors
    proc `name`[U, X](n: U, T: typedesc[Metavar[`dst`, X]]): T =
      genProcessor(n.index, T.N)

  # if the body doesn't end in an expression, add a call to the
  # entry processor
  if def.body[^1].kind == nnkProcDef:
    # ^^ a heuristic, but should work okay enough
    def.body.add newCall(ident"->", def.params[1][0],
      newDotExpr(newDotExpr(dst, ident"meta"), ident"entry"))

  def.body = newStmtList(preamble, def.body)

  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)
  lambda.params[0] = dstnterm
  lambda.params[1][^2] = srcnterm

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  call[1] = nnkObjConstr.newTree(srcnterm,
    nnkExprColonExpr.newTree(ident"index", call[1]))
  result = assemblePass(src, dst, def, call)

macro inpassImpl(name, nterm: typedesc, def: untyped) =
  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)
  lambda.params[0] = nterm

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  result = assemblePass(nil, name, def, call)

macro outpassImpl(name, nterm: typedesc, def: untyped) =
  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  result = assemblePass(name, nil, def, call)

macro inpass*(p: untyped) =
  ## Turns a procedure definition into a pass that takes arbitrary data as
  ## input and produces an AST for the specified language.
  ## The procedure's return type specifies the shape of the returned AST and
  ## must must be the non-terminal of an IL. As a short-hand, just specifying
  ## an IL is equivalent to specifying the IL's entry non-terminal.
  ##
  ## The return type of the transformed procedure is an AST.
  if p.kind != nnkProcDef:
    error(".inpass must be applied to a procedure definition", p)

  var typ = p.params[0]
  if typ.kind == nnkEmpty:
    error("a return type is required, but none is provided", p.params[0])

  result = genAst(typ, p):
    when typ is Metavar:
      inpassImpl(typ.L, typ, p)
    else:
      # use the entry non-terminal
      inpassImpl(typ, typ.meta.entry, p)

macro pass*(p: untyped) =
  ## Turns a procedure definition into a language->language pass, that is a
  ## pass, that takes an AST (fragment) of language A and produces an AST of
  ## language B.
  if p.kind != nnkProcDef:
    error(".inpass must be applied to a procedure definition", p)

  var target = p.params[0]
  if target.kind == nnkEmpty:
    error("a return type is required, but none is provided", p.params[0])
  if p.params.len == 1:
    error("the input parameter is missing", p.params)

  result = genAst(input = p.params[1][^2], target, p):
    when target is Metavar:
      passImpl(input, target.L, input, target, p)
    else:
      # use the entry non-terminal
      passImpl(input, target, input.meta.entry, target.meta.entry, p)

macro outpass*(p: untyped) =
  ## Turns a procedure definition into a language->* pass, that is, a pass
  ## that takes an AST (fragment) of language A and produces a value.
  if p.kind != nnkProcDef:
    error(".outpass must be applied to a procedure definition", p)

  let ret = p.params[0]
  if ret.kind == nnkEmpty:
    error("a return type is required, but none is provided", ret)
  if p.params.len == 1:
    error("the input parameter is missing", p.params)

  result = genAst(typ = p.params[1][^2], p):
    when typ is Metavar:
      outpassImpl(typ, typ, p)
    else:
      # use the entry non-terminal
      outpassImpl(typ, typ.entry, p)
