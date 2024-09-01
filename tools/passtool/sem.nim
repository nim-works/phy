## Implements the semantic analysis for the parsed rules.

import
  std/[os, sets, streams, tables],
  grammar,
  parser

type
  Errors* = object
    ## Accumulates errors during analysis of grammar.
    files: seq[string]
      ## list of file paths; indexed into by SourcePos
    errors: seq[tuple[pos: SourcePos, str: string]]

    currFile: uint16
      ## index of the current file

  Languages* = Table[string, Grammar]

proc emit(e: var Errors, pos: SourcePos, str: sink string) =
  e.errors.add (pos, str)

proc emit(e: var Errors, line, col: int, str: sink string) =
  e.errors.add ((e.currFile, line.uint16, col.uint16), str)

proc hasErrors*(e: Errors): bool =
  ## Returns whether there were any errors.
  e.errors.len > 0

iterator items*(e: Errors): tuple[file, val: string] =
  ## Returns all errors recorded with `e`.
  for it in e.errors.items:
    yield (e.files[it.pos.file] & "(" & $it.pos.line & ", " & $it.pos.col & ")",
           it.str)

proc semExpr(e: ParsedRule, errors: var Errors): Expr

proc semRule(rule: var Rule, e: ParsedRule, errors: var Errors) =
  case e.kind
  of SExpr, Reference:
    rule.expr = semExpr(e, errors)
  of OneOrMore:
    rule.repeat = rOneOrMore
    rule.expr = semExpr(e.sub[0], errors)
  of ZeroOrMore:
    rule.repeat = rZeroOrMore
    rule.expr = semExpr(e.sub[0], errors)
  of Optional:
    rule.repeat = rZeroOrOne
    rule.expr = semExpr(e.sub[0], errors)
  of Named:
    errors.emit(e.line, e.col, "named expressions not allowed here")

proc semExpr(e: ParsedRule, errors: var Errors): Expr =
  case e.kind
  of SExpr:
    result = Expr(isRef: false, name: e.sym)
    for it in e.sub.items:
      var rule: Rule
      if it.kind == Named:
        rule.name = it.sym
        semRule(rule, it.sub[0], errors)
      else:
        semRule(rule, it, errors)

      result.rules.add rule
  of Reference:
    result = Expr(isRef: true, name: e.sym)
    # forward references are allowed, so whether a rule with the given name
    # exists cannot be checked here
  else:
    errors.emit(e.line, e.col, "unexpected: " & $e.kind)

  result.pos = (errors.currFile, e.line.uint16, e.col.uint16)

proc verify(lang: Grammar, e: Expr, errors: var Errors) =
  ## Makes sure all references name existing rules, emitting errors for those
  ## that don't.
  case e.isRef
  of true:
    if e.name notin lang and e.name notin ["int", "float", "string"]:
      errors.emit(e.pos, "no rule with name " & e.name & " exists")
  of false:
    for it in e.rules.items:
      verify(lang, it.expr, errors)

proc isEqual(a, b: Expr, strict: bool): bool =
  ## Compares two expressions for structural equality. If `strict` is true,
  ## the names (if any) assigned to rule expressions also have to match.
  if a.isRef != b.isRef or a.name != b.name:
    return false

  case a.isRef
  of true:
    result = true
  of false:
    if a.rules.len == b.rules.len:
      for i, it in a.rules.pairs:
        let o = b.rules[i]
        # a sub-expression doesn't match -> the expressions are not equal
        if (strict and it.name != o.name) or it.repeat != o.repeat or
           not isEqual(it.expr, o.expr, strict):
          return false

      result = true
    else:
      result = false

proc find(p: seq[Production], e: Expr): int =
  ## Returns the index of a production that's equal to `e`, or -1, if none is
  ## found.
  for i, it in p.pairs:
    # ignore the names of expressions when comparing expressions:
    if isEqual(it.expr, e, strict=false):
      return i

  result = -1

proc remove(p: var seq[Production], e: Expr, errors: var Errors) =
  ## Subtracts `e` from the set of `p`. If no matching production exists,
  ## an error is emitted.
  let i = find(p, e)
  if i != -1:
    p.delete(i)
  else:
    errors.emit(e.pos, "missing rule: " & $e)

proc add(p: var seq[Production], e: sink Production, errors: var Errors) =
  ## Adds `e` to the set of productions `p`, reporting an error if this would
  ## result in a duplicate.
  let i = find(p, e.expr)
  # TODO: also make sure that the production does not lead to ambiguity
  if i == -1:
    p.add e
  else:
    errors.emit(e.expr.pos):
      "production '" & $e.expr & "' already exists, registered by " &
      p[i].source

proc sem*(name, dir: string, langs: var Languages, errors: var Errors)

proc sem(parsed: seq[Parsed], name, dir: string, langs: var Languages,
         errors: var Errors) =
  ## Analyses the parsed items, which means checking the parsed rules and
  ## productions for semantic errors and translating them into the grammar IR.
  var lang = default(Grammar)

  for it in parsed.items:
    case it.kind
    of pkDef:
      if it.name in lang:
        errors.emit(it.line, it.col, "redefinition of " & it.name)
      elif it.name in ["int", "float", "string"]:
        errors.emit(it.line, it.col):
          it.name & " is already the name of a built-in rule"
      else:
        var p: seq[Production]
        for r in it.prod.items:
          add(p, Production(source: name, expr: semExpr(r, errors)), errors)

        lang[it.name] = p
    of pkAppend:
      if it.name in lang:
        # append the given productions to the existing rule:
        for r in it.prod.items:
          let e = Production(source: name, expr: semExpr(r, errors))
          add(lang[it.name], e, errors)
      else:
        errors.emit(it.line, it.col, "no rule with name: " & it.name)
    of pkRemove:
      if it.name in lang:
        # remove the given productions from the existing rule:
        for r in it.prod.items:
          remove(lang[it.name], semExpr(r, errors), errors)
      else:
        errors.emit(it.line, it.col, "no rule with name: " & it.name)
    of pkError:
      errors.emit(it.line, it.col, "parser error: " & it.name)
    of pkImport:
      sem(it.name, dir, langs, errors)
      if lang.len > 0:
        errors.emit(it.line, it.col):
          "cannot extend language when there's already rules defined"
      else:
        # inherit the full grammar:
        lang = langs[it.name]

  for it in lang.values:
    for e in it.items:
      verify(lang, e.expr, errors)

  # add the language grammar to the table:
  langs[name] = lang

proc parseAll(file: string): seq[Parsed] =
  ## Opens the given ``.md`` file and extracts and parses all ``grammar``
  ## sections.
  var f = openFileStream(file, fmRead)
  var L = Lexer()
  openWithMarkdown(L, f)
  for p in L.parse():
    result.add p
  close(L)

proc sem*(name, dir: string, langs: var Languages, errors: var Errors) =
  ## Parses the file containing the grammar for the language with the given
  ## `name`, analyzes the result, and registers the language in `langs`. Errors
  ## are recorded to `errors`.
  let
    file = changeFileExt(dir / name, ".md")
    parsed = parseAll(file)
    prev = errors.currFile

  # register the file:
  errors.currFile = errors.files.len.uint16
  errors.files.add file

  sem(parsed, name, dir, langs, errors)

  # restore previous context:
  errors.currFile = prev

proc mark(e: Expr, marker: var HashSet[string], next: var seq[string]) =
  ## Registers all references in `e` with `marker`, adding them to `next` if
  ## not seen prior.
  if e.isRef:
    if e.name notin ["int", "float", "string"]:
      if not marker.containsOrIncl(e.name):
        next.add e.name
  else:
    for it in e.rules.items:
      mark(it.expr, marker, next)

proc trim*(langs: var Languages, errors: var Errors) =
  ## Removes unused production rules, producing errors for unused rules that
  ## were introduced specifically for the grammar they're unused in.
  var next: seq[string] # re-use across loops

  for name, it in langs.mpairs:
    var marker: HashSet[string]

    if "top" in it:
      marker.incl "top"
      next.add "top"

    # mark everything reachable from the top rule:
    while next.len > 0:
      let n = next.pop()
      for rule in it[n].items:
        mark(rule.expr, marker, next)

    var remove: seq[string]
    # register for removal everything that wasn't marked:
    for pname, prods in it.pairs:
      if pname notin marker:
        remove.add pname

        for prod in prods.items:
          if prod.source == name:
            errors.emit(prod.expr.pos, "unused production")

    for r in remove.items:
      it.del(r)
