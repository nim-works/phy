## Implements a macro DSL for constructing meta-language language definitions.
## The DSL tries to stay close to the underlying data representation for
## language definitions provided by `types <types.html>`_.

import
  types,
  std/[macros, tables, strutils, strformat]

type
  SymKind = enum
    skRelation
    skNonTerminal
    skFunc
    skTree
    skExpr
    skPattern

  Sym = object
    ## Internal type to help with symbol resolution.
    id: int
    case kind: SymKind
    of skRelation:
      params: seq[bool]
        ## the parameter information for relations. Duplicates the state from
        ## `Relation`, but this saves us from having to make list of relations
        ## available everywhere their parameters are queried
    of skPattern:
      n: TreeNode
    of skExpr:
      e: ExprNode
    of skFunc, skNonTerminal, skTree:
      discard

  Context = object
    ## Keeps track of all variables and associated information.
    disallowBind: bool
      ## 'true' when creating a binding is disallowed in the current context
    depth: int
      ## the number of enclosing repetitions
    map: Table[string, int]
      ## identifier -> variable ID
    vars: seq[tuple[pat: TreeNode, depth: int]]
      ## for each variable the backing pattern and repetition nesting

using
  lookup: Table[string, Sym]
  c: Context

proc name(n: NimNode): string =
  case n.kind
  of nnkIdent:     n.strVal
  of nnkAccQuoted: name n[0]
  else:            (error("not an identifier", n); "")

proc ellipsis(n: NimNode): NimNode =
  if n.kind == nnkPrefix and n[0].strVal == "...":
    n[1]
  else:
    nil

proc parseIdent(lookup; c: var Context, n: NimNode): TreeNode =
  ## Resolves an identifier appearing in a non-tree slot in a term or pattern.
  case n.kind
  of nnkIdent:
    var name = n.strVal
    if name == "_":
      return TreeNode(kind: nkAny)

    let sub = name.find('_')
    if sub != -1:
      name = substr(name, 0, sub-1)

    if n.strVal in c.map:
      result = TreeNode(kind: nkVar, id: c.map[n.strVal])
    else:
      if name in lookup:
        let s {.cursor.} = lookup[name]
        case s.kind
        of skNonTerminal:
          result = TreeNode(kind: nkNonTerminal, id: s.id)
        of skPattern:
          result = s.n
        else:
          error("only non-terminals or special pattern names may be used here",
                n)
      else:
        error("undeclared identfier: " & name, n)

      if sub != -1:
        if c.disallowBind:
          error("first use of variable, but binding is disabled", n)

        c.map[n.strVal] = c.vars.len
        c.vars.add (result, c.depth)
        result = TreeNode(kind: nkBind,
          children: @[TreeNode(kind: nkVar, id: c.vars.high), result])

  of nnkAccQuoted:
    n.expectLen 1
    result = parseIdent(lookup, c, n[0])
  else:
    error("expected identifier", n)

proc register(lookup: var Table[string, Sym], name: NimNode) =
  var name = name
  if name.kind == nnkAccQuoted:
    name = name[0]
  name.expectKind nnkIdent
  if name.strVal in lookup:
    # redefining an AST node kind is fine
    if lookup[name.strVal].kind != skTree:
      error("redefinition of " & name.strVal, name)
  else:
    lookup[name.strVal] = Sym(kind: skTree)

proc checkVar(c; id: int, depth: int, info: NimNode) =
  if c.vars[id].depth > depth:
    error(fmt"usage of variable requires at least {c.vars[id].depth} unpack operations",
          info)

proc scanPattern(lookup: var Table[string, Sym], n: NimNode) =
  ## Scans the body of a non-terminal for tree identifiers, adding
  ## them to `lookup` (or reporting an error).
  case n.kind
  of nnkCall:
    if n[0].kind in {nnkIdent, nnkAccQuoted}:
      register(lookup, n[0])
    for i in 1..<n.len:
      scanPattern(lookup, n[i])
  else:
    for it in n.items:
      scanPattern(lookup, it)

proc parseTerm(lookup; c; n: NimNode; depth = 0; adhoc = false): TreeNode =
  ## Recursively parses a term from `n`. To keep later post-processing simpler,
  ## variables used in the term are bound already. `adhoc` being set to false
  ## enables an error being reported for AST symbols missing in `lookup`.
  template recurse(n: NimNode; depth = depth): TreeNode =
    parseTerm(lookup, c, n, depth, adhoc)

  case n.kind
  of nnkIdent:
    var name = n.strVal
    if name in c.map:
      let id = c.map[name]
      checkVar(c, id, depth, n)
      result = TreeNode(kind: nkVar, id: id)
    else:
      error("not the name of a variable", n)
  of nnkStrLit:
    result = TreeNode(kind: nkSymbol, sym: n.strVal)
  of nnkAccQuoted, nnkPar:
    result = recurse(n[0])
  of nnkTupleConstr:
    n.expectMinLen 1
    result = TreeNode(kind: nkList)
    for it in n.items:
      result.add recurse(it)
  of nnkIntLit:
    result = TreeNode(kind: nkNumber, sym: $n.intVal)
  of nnkFloatLit:
    result = TreeNode(kind: nkSymbol, sym: $n.floatVal)
  of nnkPrefix:
    if n[0].eqIdent("..."):
      result = TreeNode(kind: nkUnpack)
      if n[1].kind == nnkBracket:
        result.add TreeNode(kind: nkGroup)
        for i in 0..<n[1].len:
          result.children[0].add recurse(n[1][i], depth + 1)
      else:
        result.add recurse(n[1], depth + 1)
    elif n[0].eqIdent("+") or n[0].eqIdent("*") or n[0].eqIdent("!"):
      error("patterns are not allowed in a non-pattern context", n)
    else:
      error("unknown prefix", n)
  of nnkCall:
    n[0].expectKind {nnkIdent, nnkAccQuoted}
    let head = name(n[0])
    result = TreeNode(kind: nkTree)
    # the tree symbol may be a variable
    if head in c.map:
      result.add TreeNode(kind: nkVar, id: c.map[head])
    elif adhoc or lookup.getOrDefault(head).kind == skTree:
      result.add TreeNode(kind: nkSymbol, sym: head)
    else:
      error("not the name of an AST symbol", n[0])
    for i in 1..<n.len:
      result.add recurse(n[i])
  of nnkBracketExpr:
    result = TreeNode(kind: nkPlug)
    result.add recurse(n[0])
    result.add recurse(n[1])
  of nnkCurly:
    result = TreeNode(kind: nkSet)
    for it in n.items:
      result.add recurse(it)
  of nnkTableConstr:
    result = TreeNode(kind: nkMap)
    for it in n.items:
      it.expectKind nnkExprColonExpr
      let e = TreeNode(kind: nkMapEntry, children: @[recurse(it[0]), recurse(it[1])])
      # reject illegal unpacks early. Either both the key and value must use
      # unpacking, or only the key.
      if e[1].kind == nkUnpack and e[0].kind != nkUnpack:
        error("inconsistent use of unpacking", it[1])
      result.add e
  else:
    error("invalid expression", n)

proc parsePattern(lookup: Table[string, Sym], c: var Context, n: NimNode): TreeNode =
  template dontBind(body: untyped) =
    var b = true
    c.disallowBind.swap(b)
    body
    c.disallowBind.swap(b)

  case n.kind
  of nnkIdent:
    result = parseIdent(lookup, c, n)
  of nnkStrLit:
    # a quoted symbol
    result = TreeNode(kind: nkSymbol, sym: n.strVal)
  of nnkAccQuoted:
    result = parsePattern(lookup, c, n[0])
  of nnkPar:
    # only used for modifying associativity, skip
    result = parsePattern(lookup, c, n[0])
  of nnkBracketExpr:
    # plug function application
    n.expectLen 2
    let arg = parsePattern(lookup, c, n[0])
    result = TreeNode(kind: nkPlug, children: @[arg, parsePattern(lookup, c, n[1])])
  of nnkBracket:
    n.expectMinLen 1
    result = TreeNode(kind: nkGroup)
    for it in n.items:
      result.add parsePattern(lookup, c, it)
  of nnkPrefix:
    n.expectLen 2
    if n[0].eqIdent("+"):
      inc c.depth
      result = node(nkOneOrMore, parsePattern(lookup, c, n[1]))
      dec c.depth
    elif n[0].eqIdent("*"):
      inc c.depth
      result = node(nkZeroOrMore, parsePattern(lookup, c, n[1]))
      dec c.depth
    elif n[0].eqIdent("!"):
      dontBind:
        result = node(nkNot, parsePattern(lookup, c, n[1]))
    elif n[0].eqIdent("..."):
      error("unpacking is not allowed in pattern")
    else:
      error("unknown prefix", n)
  of nnkInfix:
    n.expectLen 3
    if n[0].eqIdent("or"):
      let a = parsePattern(lookup, c, n[1])
      let b = parsePattern(lookup, c, n[2])
      result = TreeNode(kind: nkChoice)
      # merge choices into a single tree:
      if a.kind == nkChoice:
        result.children.add a.children
      else:
        result.add a

      # same for the second operand:
      if b.kind == nkChoice:
        result.children.add b.children
      else:
        result.add b
    else:
      error("unknown infix", n)
  of nnkTupleConstr:
    # somewhat confusingly, a tuple constructor is used as the list constructor
    n.expectMinLen 1
    result = TreeNode(kind: nkList)
    for it in n.items:
      result.add parsePattern(lookup, c, it)
  of nnkTableConstr:
    result = TreeNode(kind: nkMap)
    for it in n.items:
      it.expectKind nnkExprColonExpr
      let key = parsePattern(lookup, c, it[0])
      let val = parsePattern(lookup, c, it[1])
      # either both the key and value must use unpacking, or only the key.
      if val.kind == nkUnpack and key.kind != nkUnpack:
        error("inconsistent use of unpacking", it[1])
      result.add TreeNode(kind: nkMapEntry, children: @[key, val])
  of nnkCurly:
    error("set constructor must not be part of patterns", n)
  of nnkCall:
    result = TreeNode(kind: nkTree)
    n[0].expectKind {nnkIdent, nnkAccQuoted}
    # is it a tree symbol?
    if lookup.getOrDefault(name(n[0])).kind == skTree:
      result.add TreeNode(kind: nkSymbol, sym: name(n[0]))
    else:
      # must be the 'any' pattern otherwise
      let p = parseIdent(lookup, c, n[0])
      if p.kind != nkAny and (p.kind == nkBind and p[1].kind != nkAny):
        error("only the 'any' pattern or a tree symbols may appear here", n[0])
      result.add p

    for i in 1..<n.len:
      result.add parsePattern(lookup, c, n[i])
  of nnkIntLit:
    result = TreeNode(kind: nkNumber, sym: $n.intVal)
  else:
    error("not a valid pattern expression", n)

proc parsePremise(lookup; c: var Context, n: NimNode): Premise =
  var n = n
  # premises may be wrapped in an ellipsis, which designates them as being
  # repeated
  let e = ellipsis(n)
  if e != nil:
    n = e
    result.repeat = true
  if n.kind == nnkPar:
    n = n[0]

  n.expectKind nnkCallKinds
  n[0].expectKind nnkIdent
  if n[0].strVal in lookup:
    let depth = (if result.repeat: 1 else: 0)
    let val {.cursor.} = lookup[n[0].strVal]
    if val.kind == skRelation:
      n.expectLen 1 + val.params.len
      result.rel = val.id
      for i in 1..<n.len:
        if val.params[i - 1]:
          result.inputs.add parseTerm(lookup, c, n[i], depth)
        else:
          c.depth += depth
          result.outputs.add parsePattern(lookup, c, n[i])
          c.depth -= depth
    else:
      error("expected name of relation", n[0])
  else:
    error("undeclared identifier", n[0])

proc parseExpr(lookup; c; n: NimNode; depth=0; allowIdent=false): ExprNode =
  ## If `allowIdent` is true, identifiers that don't bind to any symbol are
  ## treated as a term symbol, otherwise they result in an error being
  ## reported. `depth` keeps track of how many enclosing repetitions there
  ## are.
  template recurse(n; depth=depth; allowIdent=false): ExprNode =
    parseExpr(lookup, c, n, depth, allowIdent)

  case n.kind
  of nnkIdent, nnkAccQuoted:
    let name = n.strVal
    if name in c.map:
      let id = c.map[name]
      checkVar(c, id, depth, n)
      result = ExprNode(kind: ekVar, id: id)
    elif name in lookup:
      let s = lookup[name]
      if s.kind == skFunc:
        result = ExprNode(kind: ekFunc, id: s.id)
      elif s.kind == skExpr:
        result = s.e
      else:
        error("not the name of a variable or function", n)
    elif allowIdent:
      # okay, treat as a symbol
      result = ExprNode(kind: ekIdent, ident: name)
    else:
      error("not the name of a variable or function", n)
  of nnkStrLit, nnkIntLit:
    # auto-treat as term because it's unambiguous
    result = ExprNode(kind: ekTerm, term: parseTerm(lookup, c, n))
  of nnkPar:
    result = recurse(n[0])
  of nnkBracket:
    result = ExprNode(kind: ekGroup)
    for it in n.items:
      result.add recurse(it)
  of nnkPrefix:
    if n[0].strVal == "...":
      result = exprNode(ekUnpack, recurse(n[1], depth + 1))
    else:
      # treat as a normal application
      let s = recurse(n[0], allowIdent=true)
      result = exprNode(ekApp, s)
      for i in 1..<n.len:
        result.add recurse(n[i])
  of nnkDotExpr:
    result = ExprNode(kind: ekLookup)
    result.add recurse(n[0])
    result.add ExprNode(kind: ekIdent, ident: n[1].strVal)
  of nnkCallKinds - {nnkPrefix}:
    if n[0].eqIdent("term"):
      n.expectLen 2
      result = ExprNode(kind: ekTerm, term: parseTerm(lookup, c, n[1]))
    elif n[0].kind in {nnkIdent, nnkAccQuoted} and
         lookup.getOrDefault(name(n[0])).kind == skTree:
      # unambiguous; can treat as term
      result = ExprNode(kind: ekTerm, term: parseTerm(lookup, c, n))
    else:
      let s = recurse(n[0], allowIdent=true)
      result = exprNode(ekApp, s)
      for i in 1..<n.len:
        result.add recurse(n[i])
  of nnkTableConstr, nnkCurly:
    # automatically treat table and set constructors as terms
    result = ExprNode(kind: ekTerm, term: parseTerm(lookup, c, n))
  else:
    error("invalid expression", n)

proc parsePredicate(lookup; c: var Context, n: NimNode): Predicate =
  if n[0].eqIdent("premise"):
    n.expectLen 2
    Predicate(kind: pkPremise,
              premise: parsePremise(lookup, c, n[1]))
  elif n[0].eqIdent("where"):
    n.expectLen 3
    Predicate(kind: pkWhere,
              pat: parsePattern(lookup, c, n[1]),
              term: parseExpr(lookup, c, n[2]))
  elif n[0].eqIdent("condition"):
    n.expectLen 2
    Predicate(kind: pkSideCondition,
              expr: parseExpr(lookup, c, n[1]))
  else:
    error("expected premise/where/condition", n)
    Predicate()

proc parseRelation(lookup; n: NimNode, rel: var Relation) =
  ## Parses and verifies the body of a relation.
  let body = n[3]
  body.expectKind nnkStmtList
  for it in body.items:
    case it.kind
    of nnkCallKinds:
      var
        rule = Rule()
        c = Context()
      case it[0].strVal
      of "axiom":
        it.expectLen 2 + rel.params.len
        it[1].expectKind nnkStrLit
        rule.name = it[1].strVal
        for i in 2..<it.len:
          if rel.params[i - 2]:
            # inputs must be patterns
            rule.conclusion.add parsePattern(lookup, c, it[i])
          else:
            # outputs must be terms
            rule.conclusion.add parseTerm(lookup, c, it[i])
      of "rule":
        it.expectLen 3
        it[1].expectKind nnkStrLit
        rule.name = it[1].strVal
        rule.conclusion.newSeq(rel.params.len)

        # processing needs to happen in the correct order, so that the
        # variables are available when needed by premise/where/condition
        # clauses. Process the conclusion input patterns first, as they can
        # bind variables
        for x in it[2].items:
          if x.kind in nnkCallKinds and x[0].eqIdent("conclusion"):
            x.expectLen 1 + rel.params.len
            for i in 1..<x.len:
              if rel.params[i - 1]:
                rule.conclusion[i - 1] = parsePattern(lookup, c, x[i])
            # the output terms are processed in the second pass

        var hasConclusion = false
        # the second pass:
        # * makes sure the syntax is correct everywhere
        # * parses and validates the terms / patterns
        for x in it[2].items:
          case x.kind
          of nnkCallKinds:
            x[0].expectKind nnkIdent
            if x[0].eqIdent("conclusion"):
              if hasConclusion:
                error("rule must only have a single conclusion", x)

              hasConclusion = true
              for i in 1..<x.len:
                if not rel.params[i - 1]:
                  # outputs must be terms
                  rule.conclusion[i - 1] = parseTerm(lookup, c, x[i])
            else:
              rule.predicates.add parsePredicate(lookup, c, x)
          of nnkCommentStmt:
            discard # TODO: implement
          else:
            error("expected call syntax or comment", x)

        if not hasConclusion:
          error("rule is missing a conclusion", it)
      else:
        error("expected axiom or rule", it)

      rel.rules.add rule
    of nnkCommentStmt:
      discard # TODO: implement
    else:
      error("expected declaration or comment", it)

proc parseNonTerminal(lookup; body: NimNode): TreeNode =
  var c = Context(disallowBind: true)
  if body.kind == nnkStmtList:
    # treat each statement/line as its own choice branch
    result = TreeNode(kind: nkChoice)
    for it in body.items:
      result.add parsePattern(lookup, c, it)
  else:
    result = parsePattern(lookup, c, body)

proc parseFunction(lookup; def: NimNode): Function =
  result = Function(name: $def[1])
  for it in def[3].items:
    case it.kind
    of nnkCommentStmt:
      # TODO: implement
      discard
    of nnkAsgn:
      let left = it[0]
      left.expectKind nnkCallKinds
      if not left[0].eqIdent(result.name):
        error(fmt"name must be '{result.name}'", left[0])

      var
        impl = FunctionImpl()
        c = Context()

      for i in 1..<left.len:
        impl.params.add parsePattern(lookup, c, left[i])

      case it[1].kind
      of nnkBlockStmt:
        let body = it[1][1]
        body.expectKind nnkStmtList
        body.expectMinLen 1
        # everything prior to the result must be a predicate
        for j in 0..<body.len-1:
          body[j].expectKind nnkCallKinds
          let x = body[j]
          impl.predicates.add parsePredicate(lookup, c, x)
        impl.output = parseExpr(lookup, c, body[^1])
      else:
        impl.output = parseExpr(lookup, c, it[1])
      result.impls.add impl
    else:
      error(fmt"expected assignment of the form `{result.name}(...) = ...`",
            it)

proc parseRelationHeader(n: NimNode): Relation =
  n.expectLen 4
  n[1].expectKind nnkCallKinds
  n[2].expectKind nnkStrLit

  result = Relation(name: name(n[1][0]), format: n[2].strVal)
  # parse the input/output specification:
  for i in 1..<n[1].len:
    case n[1][i].kind
    of nnkIdent:
      # cannot use 'in', because that's a special token only usable as an
      # infix :(
      if n[1][i].eqIdent("inp"):
        result.params.add true
    of nnkMutableTy:
      n[1][i].expectLen 0
      result.params.add false
    else:
      error("expected either 'inp' or 'out'", n[1][i])

macro language*(body: untyped): Language =
  ## Parses the language definition `body` and returns it as a ``Language``
  ## object. All symbol resolution errors are reported and some basic sanity
  ## checks for variable binding is performed.
  body.expectKind nnkStmtList

  var
    lang = Language()
    lookup: Table[string, Sym]

  # add the built-in symbols:
  lookup["hole"] = Sym(kind: skPattern, n: TreeNode(kind: nkHole))
  lookup["any"] = Sym(kind: skPattern, n: TreeNode(kind: nkAny))
  lookup["z"] = Sym(kind: skPattern, n: TreeNode(kind: nkAnyInt))
  lookup["r"] = Sym(kind: skPattern, n: TreeNode(kind: nkAnyRational))
  lookup["symbol"] = Sym(kind: skPattern, n: TreeNode(kind: nkAnySymbol))

  proc addSym(lookup: var Table[string, Sym], name: sink string, n: NimNode,
              s: sink Sym) {.nimcall.} =
    if name in lookup:
      error("redeclaration of " & name, n)
    lookup[name] = s

  # first pass: make sure the broad shape of the body is correct and collect
  # the names of all symbols while looking for and reporting collisions
  for it in body.items:
    if it.kind in nnkCallKinds:
      it[0].expectKind nnkIdent
      case it[0].strVal
      of "inductive":
        let rel = parseRelationHeader(it)
        addSym(lookup, rel.name, it):
          Sym(kind: skRelation, id: lang.relations.len, params: rel.params)
        lang.relations.add rel
      of "nterminal":
        it.expectLen 3
        addSym(lookup, name(it[1]), it):
          Sym(kind: skNonTerminal, id: lang.nterminals.len)
        lang.nterminals.add NonTerminal(name: it[1].strVal)
        scanPattern(lookup, it[2])
      of "function":
        it.expectLen 4
        addSym(lookup, name(it[1]), it):
          Sym(kind: skFunc, id: lang.functions.len)
        lang.functions.add Function(name: $it[1])
      of "alias":
        it.expectLen 3
        var dummy = Context()
        # aliases are inlined on use (leaving no trace of their existence)
        # and thus their content has to be parsed early
        addSym(lookup, name(it[1]), it):
          Sym(kind: skExpr, e: parseExpr(lookup, dummy, it[2]))
      else:
        error("expected 'alias', 'nterminal', 'function', or 'inductive'", it)
    elif it.kind == nnkCommentStmt:
      # TODO: process
      discard
    else:
      error("expected declaration or doc comment", it)

  # second pass: process the body of all declarations
  for it in body.items:
    if it.kind in nnkCallKinds:
      case it[0].strVal
      of "inductive":
        parseRelation(lookup, it, lang.relations[lookup[name(it[1][0])].id])
      of "nterminal":
        lang.nterminals[lookup[name(it[1])].id].pattern =
          parseNonTerminal(lookup, it[2])
      of "function":
        lang.functions[lookup[name(it[1])].id] = parseFunction(lookup, it)
    else:
      discard "nothing to do"

  result = newLit(lang)

macro term*(x: untyped): TreeNode =
  ## Turns the meta-language term `x` into its data representation.
  var c = Context()
  let ast = parseTerm(Table[string, Sym](), c, x, adhoc=true)
  result = newLit(ast)
