## Implements a macro DSL for writing formal language definitions, covering the
## grammar, static semantics, and operational semantics (though the latter is
## not yet implemented).

import std/[macros, tables]

type
  Judgement = object
    context: NimNode
    term: NimNode
    meaning: NimNode

  VarSpec = object
    name: string
    typ: NimNode

  Rule = object
    vars: seq[VarSpec]
    hypothesis: seq[Judgement]
    conditions: seq[NimNode]
    then: seq[Judgement]

proc varId(id: int) =
  ## Helper procedure for unambiguously representing var references.
  discard

proc expand(id: int) =
  ## Helper procedure for unambiguously representing seq var expansions.
  discard

proc lookup(vars: seq[VarSpec], n: NimNode, fail = true): int {.compileTime.} =
  for i, it in vars.pairs:
    if it.name == n.strVal:
      return i

  if fail:
    error("no var with the given name exists", n)

  result = -1

proc preprocess(vars: seq[VarSpec], n: NimNode, isTerm: bool): NimNode =
  ## Binds identifiers to variabes and transforms some trees in order to make
  ## later processing easier.
  template recurse(i: int) =
    n[i] = preprocess(vars, n[i], isTerm)

  case n.kind
  of nnkIdent:
    let id = lookup(vars, n, false)
    if id == -1:
      result = n # nothing to bind
    else:
      result = newCall(bindSym"varId", newIntLitNode(id))
  of nnkAccQuoted:
    result = n[0] # unwrap the quoted identifier, but don't bind anything
  of nnkBracketExpr:
    if n.len == 1:
      return newCall(bindSym"expand", newIntLitNode(lookup(vars, n[0])))
    else:
      result = n
      for i in 0..<n.len:
        recurse(i)
  of nnkCall:
    result = n
    # don't bind anything in the callee when processing a term
    for i in ord(isTerm)..<n.len:
      recurse(i)
  else:
    result = n
    for i in 0..<n.len:
      recurse(i)

proc parseRule(name, body: NimNode): Rule =
  name.expectKind nnkStrLit
  body.expectKind nnkStmtList

  result = Rule()

  # first extract all variables, conditions, and judgements:
  for it in body.items:
    case it.kind
    of nnkCommand:
      it[0].expectKind nnkIdent
      case it[0].strVal
      of "then":
        it.expectLen 4
        result.then.add:
          Judgement(context: it[1], term: it[2], meaning: it[3])
      of "condition":
        it.expectLen 2
        result.conditions.add it[1]
      of "hypothesis":
        it.expectLen 4
        result.hypothesis.add:
          Judgement(context: it[1], term: it[2], meaning: it[3])
      else:
        error("unknown statement", it[0])
    of nnkVarSection:
      for idef in it.items:
        let typ = idef[^2]
        if typ.kind != nnkIdent or typ.strVal notin ["any", "range", "seq"]:
          error("type must be `range`, `seq`, or `any`", it)

        for i in 0..<idef.len - 2:
          result.vars.add VarSpec(name: idef[i].strVal, typ: typ)
    else:
      error("statement must be of the form `n a, b, c`", it)

  # then replace identifiers with references to the variables they name

  for it in result.then.mitems:
    it.context = preprocess(result.vars, it.context, isTerm=false)
    it.term    = preprocess(result.vars, it.term,    isTerm=true)
    it.meaning = preprocess(result.vars, it.meaning, isTerm=false)

  for it in result.hypothesis.mitems:
    it.context = preprocess(result.vars, it.context, isTerm=false)
    it.term    = preprocess(result.vars, it.term,    isTerm=true)
    it.meaning = preprocess(result.vars, it.meaning, isTerm=false)

  for it in result.conditions.mitems:
    it = preprocess(result.vars, it, isTerm=false)

proc parseGrammar(body: NimNode) =
  ## Parses a ``grammar body`` declaration.
  # note: only grammars for trees are currently supported
  body.expectKind nnkStmtList

  var rules: Table[string, NimNode]

  # first pass: gather all rules
  for it in body.items:
    case it.kind
    of nnkAsgn:
      it[0].expectKind nnkIdent
      if it[0].strVal in rules:
        error("a non-terminal symbol with the same name already exists", it[0])
      else:
        rules[it[0].strVal] = it[1]
    else:
      error("expected an assignment", it)

  # second pass: make sure the tree expression are well formed and all non-
  # terminal symbols have an associated rule
  proc check(rules: Table[string, NimNode], n: NimNode) {.nimcall.} =
    case n.kind
    of nnkTupleConstr, nnkPar:
      n.expectMinLen 1
      n[0].expectKind nnkIdent # the tree kind
      for i in 1..<n.len:
        check(rules, n[i])

    of nnkPrefix:
      if eqIdent(n[0], "$") and n[1].kind == nnkIdent:
        let m = n[1]
        if not (eqIdent(m, "i") or eqIdent(m, "f") or eqIdent(m, "str")):
          error("unknown meta-variable", m)
      elif eqIdent(n[0], "*") or eqIdent(n[0], "+") or eqIdent(n[0], "?"):
        check(rules, n[1])
      else:
        error("unexpected tree", n)
    of nnkInfix:
      if eqIdent(n[0], "or"):
        check(rules, n[1])
        check(rules, n[2])
      else:
        error("unexpected tree", n)
    of nnkIdent:
      if n.strVal notin rules:
        error("missing rule for non-terminal", n)
    else:
      error("unexpected tree", n)

  for it in rules.values:
    check(rules, it)

proc parseDerived(name, body: NimNode) =
  name.expectKind nnkStrLit
  var body = body
  # unwrap single-item statement lists:
  if body.kind == nnkStmtList and body.len == 1:
    body = body[0]

  body.expectKind nnkInfix
  if not eqIdent(body[0], "->"):
    error("expression of the form `a -> b` expected", body)

  # TODO: implement validation of the operands. They need to be well-formed
  #       tree expressions

proc parseSemantics(name, body: NimNode) =
  ## Parses a ``semantics name, body`` declaration.
  name.expectKind nnkStrLit
  body.expectKind nnkStmtList

  for it in body.items:
    if it.kind == nnkCommand and it[0].eqIdent("rule") and it.len == 3:
      discard parseRule(it[1], it[2])
    else:
      error("rule of the form `rule \"...\", body` expected", it)

macro language*(name: untyped, body: untyped) =
  ## Makes sure the language definition `body` is well-formed.
  body.expectKind nnkStmtList

  for it in body.items:
    if it.kind in nnkCallKinds:
      it[0].expectKind nnkIdent
      case it[0].strVal
      of "grammar":
        it.expectLen 2
        parseGrammar(it[1])
      of "derived":
        it.expectLen 3
        parseDerived(it[1], it[2])
      of "semantics":
        it.expectLen 3
        parseSemantics(it[1], it[2])
      else:
        error("unknown declaration")
    else:
      error("declaration of the form `decl a, b` expected", it)
