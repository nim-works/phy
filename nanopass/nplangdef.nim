## Implements the language definition parsing and processing.

import std/[macros, intsets, sets, strformat, tables]
from nanopass/asts import RefTag

type
  # Core types capturing a defined language
  Elem* = object
    ## Element of a form.
    typ*: string
      ## the actual type
    repeat*: bool

  Form* = object
    ## Semantic representation of a syntax form.
    tag*: string # TODO: rename to name
    id*: int
      ## the integer ID through which a tree node is identified as being an
      ## instance of the form
    elems*: seq[Elem]

  OrigForm* = object
    ## Source-level-ish representation of a syntax form description.
    vars*: seq[string]
      ## the metavars-as-written for the form's elements
    semantic*: int
      ## index of the semantic representation

  Terminal* = object
    mvars*: seq[string]
      ## the meta-variables for ranging over values of the type
    tag*: int
      ## the integer ID through which a tree node is identified as being
      ## an instance of the terminal

  NonTerminal* = object
    mvars*: seq[string]
      ## the meta-variables for ranging over the productions
    vars*: seq[string]
      ## meta-variables used as productions
    forms*: seq[OrigForm]
      ## forms used as productions

  Record* = object
    mvars*: seq[string]
      ## the meta-variables for ranging over the record instances
    tag*: int
      ## the integer ID through which a tree node is identified as
      ## storing a reference to an instance of the record
    fields*: seq[tuple[name, mvar, typ: string]]

  LangDef* = object
    ## A checked and pre-processed language definition, carrying enough
    ## source-level information necessary for implementing, e.g., inheritance.
    terminals*: Table[string, Terminal]
      ## the terminals of the language
    nterminals*: Table[string, NonTerminal]
      ## the non-terminals of the language
    records*: Table[string, Record]
      ## the records of the language
    forms*: seq[Form]
      ## all syntax forms present in the language
    entry*: string
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

  RecordDef = object
    ## Pre-processed record definition.
    name: NimNode
    sub: seq[NimNode]
    add: seq[NimNode]

const
  FirstTerminalTag* = RefTag + 1
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
  elif name in target.records:
    error(fmt"record with name '{name}' already exists", info)
  elif name in target.nterminals:
    error(fmt"non-terminal with name {name} already exists", info)
  elif name in vars:
    error(fmt"'{name}' is already the name of a meta-variable for '{vars[name]}'", info)

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

  for it in def.records.mvalues:
    if it.tag == -1:
      it.tag = next
      inc next

proc buildLanguage(add, sub: seq[NimNode],
                   def: seq[NonTerminalDef],
                   records: seq[RecordDef],
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

  proc processTerminal(n: NimNode): string =
    n.expectKind nnkCall
    n.expectMinLen 2
    n[0].expectKind nnkIdent
    for i in 1..<n.len:
      n[i].expectKind nnkIdent
    result = n[0].strVal

  # apply the terminal removals and carry over the remaining ones:
  for it in sub.items:
    let name = processTerminal(it)
    if name notin base.terminals:
      error("terminal does not exist in the base language", it)
    base.terminals.del(name)

  result.terminals = base.terminals

  var vars: Table[string, string]

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

  # apply the record field removals to the base language:
  for it in records.items:
    it.name.expectKind nnkCall
    it.name[0].expectKind nnkIdent
    let name = it.name[0].strVal
    if it.sub.len > 0:
      if name notin base.records:
        error(fmt"base language has no record named '{name}'", it.name)

      var fields = move base.records[name].fields
      for field in it.sub.items:
        let fname = field[0]
        fname.expectKind nnkIdent
        block search:
          for i in 0..<fields.len:
            if fields[i].name == fname.strVal:
              fields.delete(i)
              break search

          error(fmt"record '{name}' has no field named '{fname.strVal}'",
                fname)

      if fields.len == 0 and it.add.len == 0:
        # the record has no fields anymore -> remove it
        base.records.del(name)
      else:
        base.records[name].fields = fields

    if name in base.records:
      # remove the old meta-variables:
      base.records[name].mvars.shrink(0)

  # update the var list with the to-be-inherited meta-vars:
  for name, it in base.terminals.pairs:
    for n in it.mvars.items:
      vars[n] = name

  for name, it in base.nterminals.pairs:
    for n in it.mvars.items:
      vars[n] = name

  for name, it in base.records.pairs:
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

  for it in records.items:
    let name = it.name[0].strVal
    if name in base.records:
      for i in 1..<it.name.len:
        let mname = it.name[i].strVal
        checkName(base, vars, mname, it.name[1])
        base.records[name].mvars.add mname
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

  # inherit the records:
  for name, it in base.records.pairs:
    var res = it
    # check the type references:
    for field in res.fields.items:
      if field.mvar notin vars:
        error(fmt"cannot inherit record '{name}'; '{field.mvar}' was removed",
              info)
      elif vars[field.mvar] != field.typ:
        error(fmt"cannot inherit record '{name}'; '{field.mvar}' changed its meaning",
              info)

    result.records[name] = res

  # ---- phase 2: make all additions
  for it in add.items:
    let name = processTerminal(it)
    checkName(result, vars, name, it)
    var tm = Terminal(tag: -1)
    # the node tag is filled in later
    for i in 1..<it.len:
      let mvar = it[i].strVal
      checkName(result, vars, mvar, it)
      tm.mvars.add mvar
      vars[mvar] = name

    result.terminals[name] = tm

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

  # register the records and non-terminals first:
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

  for it in records.items:
    let name = it.name[0].strVal
    if it.add.len > 0 and name notin base.records:
      # it's a new record
      checkName(result, vars, name, it.name)
      var rec = Record(tag: -1) # the tag is computed later
      for i in 1..<it.name.len:
        checkName(result, vars, it.name[i].strVal, it.name[i])
        rec.mvars.add it.name[i].strVal
        vars[it.name[i].strVal] = name

      result.records[name] = rec

  # add the productions:
  for it in def.items:
    let name = it.name[0].strVal
    if it.add.len > 0:
      for a in it.add.items:
        addProd(result, a, name)

  # add the new record fields:
  for it in records.items:
    let name = it.name[0].strVal
    if it.add.len > 0:
      var record: Record
      # temporarily pop the record from the table, so that it can be accessed
      # more easily
      discard result.records.pop(name, record)

      for field in it.add.items:
        let fname = field[0]
        let typ = field[1]
        fname.expectKind nnkIdent
        typ.expectKind nnkIdent
        if findIt(record.fields, it.name == fname.strVal) != -1:
          error(fmt"record '{name}' already has field named '{fname.strVal}'",
                fname)

        # the type name may refer to a meta-variable, but this is resolved
        # at a later point
        if typ.strVal in vars:
          record.fields.add (fname.strVal, typ.strVal, vars[typ.strVal])
        else:
          error(fmt"no meta-var with name '{typ.strVal}' exists", typ)

      result.records[name] = record

  computeNodeTags(result)
  # TODO: properly set the entry non-terminal
  result.entry = "module"

proc makeLanguage*(body: NimNode): LangDef =
  ## Creates a language definition from the ``defineLanguage`` DSL code.
  body.expectMinLen 1
  var add: seq[NimNode]
  var def: seq[NonTerminalDef]
  var records: seq[RecordDef]

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
        if it[2].kind == nnkTupleConstr:
          var rec = RecordDef(name: it[1])
          for elem in it[2].items:
            elem.expectKind nnkExprColonExpr
            rec.add.add elem
          records.add rec
        else:
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
  buildLanguage(add, @[], def, records, default(LangDef), body)

proc makeLanguage*(base: LangDef, body: NimNode): LangDef =
  ## Creates a language definition from the ``defineLanguage`` DSL code
  ## and `base`.
  var add, sub: seq[NimNode]
  var def: seq[NonTerminalDef]
  var records: seq[RecordDef]

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
        if it[2].kind == nnkTupleConstr:
          var rec = RecordDef(name: it[1])
          it[2].expectMinLen(1)

          # the + or - prefix is part of the name slot
          for elem in it[2].items:
            elem.expectKind nnkExprColonExpr
            elem[0].expectKind nnkPrefix
            if elem[0][0].eqIdent("+"):
              rec.add.add nnkExprColonExpr.newTree(elem[0][1], elem[1])
            elif elem[0][0].eqIdent("-"):
              rec.sub.add nnkExprColonExpr.newTree(elem[0][1], elem[1])
            else:
              error("expected '+' or '-'", elem[0][0])

          records.add rec
        else:
          var nt = NonTerminalDef(name: it[1])
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

  buildLanguage(add, sub, def, records, base, body)
