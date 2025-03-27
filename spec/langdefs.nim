## Implements a macro DSL for constructing meta-language language definitions.
## The macro DSL is a front-end to the meta-language, with the macro
## implementing a type checker and (basic) transformer for it.

import
  std/[macros, tables, sets, strutils, strformat, hashes],
  rationals

# a lot of the types from ``types`` are redefined here, so everything is
# imported explicitly
from types import NodeKind, Rule, Relation, Function, LangDef, Pattern,
                  `[]`, add, withChildren, len, tree

type
  TypeKind = enum
    ## Extends ``types.TypeKind`` with some values only relevant for analysis.
    # important: the ordinal values of the shared fields must be identical; the
    # conversion logic relies on it
    tkAll, tkVoid, tkBool, tkInt, tkRat, tkList, tkFunc, tkTuple, tkRecord,
    tkData, tkSum

    tkPat  ## type of a pattern-based constructor
    tkVar  ## type variable that's not fully resolved yet
    tkForall ## forall(t..., t) - a type with variables
    tkOr   ## an existential type. **Not a sum type**

  Type = ref object
    ## A ref type is used because the shared ownership makes the type checker
    ## much easier to implement.
    case kind: TypeKind
    of tkAll, tkBool, tkInt, tkRat, tkPat, tkVoid:
      discard
    of tkVar:
      id: int
    of tkData:
      constr*: seq[types.Node[Type]]
    of tkFunc, tkTuple, tkSum, tkForall, tkList, tkOr:
      children: seq[Type]
    of tkRecord:
      fields: seq[tuple[name: string, typ: Type]]

  Node = types.Node[Type]

  SymKind = enum
    skDef
    skType
    skConstr   ## type constructor
    skContext
    skVar
    skFunc
    skRelation
    skOverload ## overloaded constructor

  Sym = ref object
    ## An identifier with attached meaning.
    case kind: SymKind
    of skOverload:
      overloads: seq[Sym]
    of skDef:
      e: Node
    of skConstr, skType, skContext, skFunc, skRelation, skVar:
      typ: Type
      id: int

  Context = object
    ## The global working-state for analysis and the type checker. Keeps track
    ## of all entities and their related state.
    lookup: Table[string, Sym]
      ## top-level lookup table
    typerelCache: Table[(Type, Type), TypeRel]
      ## remember the type relation between datatypes, to speed up queries

    depth: int
      ## the number of enclosing repetitions (relevant for patterns)
    vars: Table[string, tuple[typ: Type, id: int]]
    tvars: seq[tuple[info: NimNode, limit, curr: Type]]
      ## the inference state for all active type variables. `limit` is the
      ## upper bound for the type, and `curr` is the currently inferred type

    unpacked: seq[HashSet[int]]
      ## stack of unpack contexts. They accumulate all list variables used
      ## within unpack contexts

    # output:
    relations: seq[Relation[Type]]
    functions: seq[Function[Type]]
    matchers: seq[Pattern[Type]]

  TypeRel = enum
    ## Describes the relationship between two types.
    relEqual
    relSubtype
    relNone

  TType = types.Type
  TNode = types.Node[types.TypeId]

using
  c: var Context

const
  InTuplePat = {nkTrue, nkFalse, nkNumber, nkString, nkType, nkTuple, nkConstr}
  InConstrPat = InTuplePat + {nkGroup, nkZeroOrMore, nkOneOrMore}
  OfBranchPat = InConstrPat + {nkVar}
  AllPat = OfBranchPat + {nkPlug}

proc unreachable() {.noreturn.} =
  doAssert false, "unreachable"

proc hash(x: Type): Hash =
  hash(cast[int](x))

template `[]`(typ: Type, i: untyped): untyped =
  typ.children[i]

template fntype(frm, to: Type): Type =
  Type(kind: tkFunc, children: @[frm, to])

template tvar(x: int): Type =
  Type(kind: tkVar, id: x)

template tup(elems: varargs[Type]): Type =
  Type(kind: tkTuple, children: @elems)

template listT(elem: Type): Type =
  let typ = elem
  assert typ != nil
  Type(kind: tkList, children: @[typ])

template forall(num: int, body: Type): Type =
  var r = Type(kind: tkForall)
  for it in 0..<num:
    r.add Type(kind: tkAll)
  r.add body
  r

proc add(x: Type, y: Type) =
  assert y != nil
  x.children.add y

proc `$`(t: Type): string =
  ## Stringifies a type.
  case t.kind
  of tkAll: "all"
  of tkVoid: "void"
  of tkInt: "int"
  of tkRat: "rat"
  of tkBool: "bool"
  of tkFunc: $t[0] & " -> " & $t[1]
  of tkData: "data(...)"
  of tkList: "*" & $t[0]
  of tkPat:  "..."
  of tkVar:  "tvar:" & $t.id
  of tkTuple:
    var r = "("
    for i, it in t.children.pairs:
      if i > 0: r.add ", "
      r.add $it
    r & ")"
  of tkSum:
    var r = "("
    for i, it in t.children.pairs:
      if i > 0: r.add " + "
      r.add $it
    r & ")"
  of tkRecord:
    var r = "{"
    for i, it in t.fields.pairs:
      if i > 0: r.add ", "
      r.add it.name & ": " & $it.typ
    r & "}"
  of tkOr:
    var r = "("
    for i, it in t.children.pairs:
      if i > 0: r.add ", "
      r.add $it
    r & ")"
  of tkForall:
    unreachable()

proc name(n: NimNode): string =
  case n.kind
  of nnkIdent:
    n.strVal
  of nnkAccQuoted:
    n.expectLen 1
    name n[0]
  else:
    error("not an identifier", n)
    ""

proc newTypeVar(c; info: NimNode, limit = Type(nil)): Type =
  ## Creates and adds a new type-var to the environment.
  result = Type(kind: tkVar, id: c.tvars.len)
  # start with the top type as the upper limit and the bottom type as the
  # inferred type
  var limit = limit
  if limit.isNil:
    limit = Type(kind: tkAll)
  c.tvars.add (info, limit, Type(kind: tkVoid))

proc flushVars(c) =
  c.vars.clear()

proc ellipsis(n: NimNode): NimNode =
  if n.kind == nnkPrefix and n[0].strVal == "...":
    n[1]
  else:
    nil

proc resolveIdent(c: Context; n: NimNode): Sym =
  ## Resolves an identifier appearing in a non-constructor expression position
  ## to a symbol.
  case n.kind
  of nnkIdent:
    let name = n.strVal
    if name in c.lookup:
      c.lookup[name]
    elif name in c.vars:
      let (typ, id) = c.vars[name]
      Sym(kind: skVar, typ: typ, id: id)
    else:
      error("undeclared identifier", n)
      Sym()
  of nnkAccQuoted:
    n.expectLen 1
    resolveIdent(c, n[0])
  else:
    error("expected identifier", n)
    Sym()

proc addSym(c; name: sink string, n: NimNode, s: sink Sym) {.nimcall.} =
  if name in c.lookup:
    error("redeclaration of " & name, n)
  if '_' in name:
    error("only names of value bindings can contain underscores", n)
  c.lookup[name] = s

proc toExpr(c; s: Sym): Node =
  ## Turns the given symbol into its ``Node``-based representation.
  case s.kind
  of skDef:
    result = s.e
  of skFunc:
    result = Node(kind: nkFunc, id: s.id, typ: s.typ)
  of skRelation:
    result = Node(kind: nkRelation, id: s.id, typ: s.typ)
  of skType:
    result = Node(kind: nkType, typ: s.typ)
  of skVar:
    result = Node(kind: nkVar, id: s.id, typ: s.typ)
    # unpack lists if requested to do so
    for it in c.unpacked.mitems:
      if result.typ.kind == tkList:
        result.typ = result.typ[0]
        it.incl s.id # register the variable with the unpack context
  of skContext:
    result = Node(kind: nkContext, id: s.id, typ: s.typ)
  of skConstr:
    result = s.typ.constr[s.id][0]
  of skOverload:
    let b = s.overloads[0]
    result = b.typ.constr[b.id][0]

proc skip(c; a: Type): Type =
  ## Skips linked type variables, only returning type variables that never
  ## point to another type variable.
  result = a
  while result.kind == tkVar and c.tvars[result.id].curr.kind == tkVar:
    result = c.tvars[result.id].curr

proc finalize(c; n: var Node) =
  ## Replaces all typevars with their inferred type.
  proc collapse(c; typ: Type): Type =
    result = c.tvars[skip(c, typ).id].curr
    if result.kind == tkVoid:
      # prefer anything other than void
      result = c.tvars[skip(c, typ).id].limit

    if result.kind == tkOr:
      # caused either by a type-checker bug OR a by an overloaded constructor
      # appearing in an R-pattern. Pick the first type and hope for the best
      # XXX: this should ideally not be needed
      result = result.children[0]

  proc replaceVars(c; typ: Type) {.nimcall} =
    ## Replaces typevars in types.
    if typ.kind in {tkList, tkFunc, tkTuple, tkSum}:
      # other types cannot contain variables
      for it in typ.children.mitems:
        assert it != nil
        if it.kind == tkVar:
          it = collapse(c, it)
        else:
          replaceVars(c, it)

  proc replaceVars(c; n: var Node) {.nimcall.} =
    ## Replaces typevars in nodes.
    if n.typ != nil:
      if n.typ.kind == tkVar:
        n.typ = collapse(c, n.typ)
      else:
        replaceVars(c, n.typ)

    case n.kind
    of withChildren:
      for it in n.children.mitems:
        replaceVars(c, it)
    else:
      discard

  replaceVars(c, n)
  c.tvars.shrink(0) # remove all type variables

proc witness(n: Node): Node =
  ## Creates a witness for the pattern `n`, that is, a term for which
  ## `n` matches.
  case n.kind
  of nkSymbol, nkString, nkNumber, nkType, nkTrue, nkFalse:
    # we cheat a bit and treat `nkType` as a witness even if it isn't one
    n
  of nkHole:
    Node(kind: nkType, typ: Type(kind: tkVoid))
  of nkBind:
    if n.len == 1:
      n[0]
    else:
      witness(n[1])
  of nkPlug:
    # leave as is, which should result in the "correct" behaviour in most cases
    n
  of nkGroup, nkConstr:
    var x = Node(kind: n.kind, typ: n.typ)
    for it in n.children.items:
      if it.kind == nkZeroOrMore:
        # an empty string is a witness
        discard
      elif it.kind == nkOneOrMore:
        # a single instance of the inner pattern is enough
        let w = witness(it[0])
        if w.kind == nkGroup:
          x.children.add w.children
        else:
          x.add w
      else:
        x.add witness(it)
    x
  else:
    unreachable()

proc matchesType(c; typ: Type, n: Node): bool
proc fits(c; b, a: Type): TypeRel

proc fitsC(c; b, a: Type): TypeRel =
  ## Cached version of ``fits``.
  if b.kind != tkVar and a.kind in {tkFunc, tkRecord, tkTuple, tkData}:
    # don't cache type variable relations, as those aren't stable
    c.typerelCache.withValue (b, a), val:
      result = val[]
    do:
      result = fits(c, b, a)
      c.typerelCache[(b, a)] = result
  else:
    result = fits(c, b, a)

proc fits(c; b, a: Type): TypeRel =
  ## Reads as "is b is a subset of a". Watch out! This does potentially modify
  ## the type context when `a` or `b` involve type variables.
  if a == b:
    return relEqual
  elif a.kind == tkOr:
    # a destination 'or' type must be resolved before type variable handling
    for it in a.children.items:
      let f = fits(c, b, it)
      if f != relNone:
        # always report a subtype match to allow narrowing the owning type
        # variable
        return relSubtype
    return relNone

  case b.kind
  of tkVoid:
    # bottom type; fits all types
    return relSubtype
  of tkVar:
    let b = skip(c, b)
    if a.kind == tkVar:
      let a = skip(c, a)
      if a == b:
        return relEqual

      var min, max: Type
      # select the more general type as the lower bound
      if fitsC(c, c.tvars[b.id].curr, c.tvars[a.id].curr) != relNone:
        min = c.tvars[a.id].curr
      elif fitsC(c, c.tvars[a.id].curr, c.tvars[b.id].curr) != relNone:
        min = c.tvars[b.id].curr
      else:
        return relNone
      # select the more specific type as the upper bound
      if fitsC(c, c.tvars[b.id].limit, c.tvars[a.id].limit) != relNone:
        max = c.tvars[b.id].limit
      elif fitsC(c, c.tvars[a.id].limit, c.tvars[b.id].limit) != relNone:
        max = c.tvars[a.id].limit
      else:
        # unrelated upper bounds. Possible when the lower bound of both vars
        # is void
        return relNone

      if fitsC(c, min, max) != relNone:
        # merge the type variables by pointing one to the other
        c.tvars[a.id].limit = max
        c.tvars[a.id].curr = min
        c.tvars[b.id].limit = a
        c.tvars[b.id].curr = a
        return relEqual
      else:
        return relNone
    else:
      let f = fitsC(c, c.tvars[b.id].curr, a)
      if f != relNone and fitsC(c, a, c.tvars[b.id].limit) == relSubtype:
        # narrow down the upper limit of the inferred type
        c.tvars[b.id].limit = a
      return f
  of tkOr:
    for it in b.children.items:
      let f = fitsC(c, it, a)
      if f != relNone:
        return relSubtype
    return relNone
  else:
    discard "no special handling"

  proc merge(a: var TypeRel, b: TypeRel) =
    if relNone in {a, b} or b != relEqual:
      a = b

  case a.kind
  of tkAll:
    if b.kind == tkAll: relEqual
    else:               relSubtype
  of tkVoid:
    relNone
  of tkInt, tkBool:
    if a.kind == b.kind: relEqual
    else:                relNone
  of tkRat:
    case b.kind
    of tkRat: relEqual
    of tkInt: relSubtype
    else:     relNone
  of tkList:
    if b.kind == tkList: fitsC(c, b[0], a[0])
    else:                relNone
  of tkRecord:
    # record types are always named, and thus an identity comparison is enough
    if b.kind == tkRecord and a == b:
      relEqual
    else:
      relNone
  of tkTuple, tkFunc:
    if a.kind == b.kind and a.children.len == b.children.len:
      var f = relNone
      for i, it in b.children.pairs:
        f.merge(fitsC(c, it, a[i]))
        if f == relNone:
          return relNone
      f
    else:
      relNone
  of tkVar:
    let b = skip(c, b)
    let f =
      if c.tvars[a.id].limit != nil: fitsC(c, b, c.tvars[a.id].limit)
      else: relSubtype

    if f != relNone:
      if c.tvars[a.id].curr.isNil or fitsC(c, b, c.tvars[a.id].curr) == relNone:
        # conservatively assume that the type will be generalized later:
        c.tvars[a.id].curr = b
      relSubtype
    else:
      relNone
  of tkData:
    if b.kind == tkData:
      # every construction that's part of `b` must also be part of `a` (but
      # not the other way around)
      for it in b.constr.items:
        if not matchesType(c, a, it):
          return relNone
      relSubtype
    else:
      relNone
  of tkSum:
    if b.kind == tkSum:
      for it in b.children.items:
        if fits(c, it, a) == relNone:
          return relNone
      relSubtype
    else:
      for it in a.children.items:
        if fits(c, b, it) != relNone:
          return relSubtype
      relNone
  else:
    unreachable()

proc check(c; a, b: Type, info: NimNode) =
  if fitsC(c, b, a) == relNone:
    error(fmt"type mismatch. Expected {a}, got {b}", info)

proc matchesPattern(c; pat, term: Node): bool

proc matchesList(c; pat, term: Node): bool =
  ## Tests whether the list-like pattern matches for the list-like expression
  ## `term`.
  # fairly complex implementation based on continuation-passing-style. The
  # main complexity is due to `term` possibly containing "meta" elements
  # (e.g., repetition patterns) and transparently nested terms, which requires
  # a dedicated cursor data structure and loop tracking (in the form of the
  # start cursor)
  type
    Cursor = object
      parent: ptr Cursor
      node: ptr Node # a pointer in order to prevent a copy
      pos: int
    Cont = proc(c: var Context, term, start: Cursor): bool

  const RepLike = {nkUnpack, nkZeroOrMore, nkOneOrMore}

  proc next(term: Cursor): Cursor =
    result = term
    inc result.pos
    # when reaching the end of a list, go one step up
    while result.pos >= result.node[].len and result.parent != nil:
      if result.node.kind in RepLike:
        result = result.parent[]
        # don't advance the position. Unless someone outside breaks out of it,
        # this lead to the repetition to be visited again and again
      else:
        result = result.parent[]
        inc result.pos

  proc hasNext(term: Cursor): bool =
    term.pos < term.node[].len

  proc get(term: Cursor): lent Node =
    term.node[][term.pos]

  proc matches(c; pat: Node, term, start: Cursor, then: Cont): bool =
    proc rep(c; pat: Node, term, start: Cursor, then: Cont): bool =
      matches(c, pat, term, start,
        proc(c; term, nstart: Cursor): bool =
          if nstart.node != nil and nstart.node == start.node:
            if addr(term.get()) == start.node:
              # the pattern and term loop converge, meaning that the term
              # repetition is consumed
              rep(c, pat, next(term), Cursor(), then)
            else:
              # the pattern and term loop don't converge after the first
              # iteration. The logic to handle this case is missing, so we
              # atleast report an error indicating what's wrong
              error("pattern and term combination is too complex")
              unreachable()
          else:
            rep(c, pat, term, nstart, then)) or
        then(c, term, start)

    # clear out the start cursor when entering a repetition pattern, to ensure
    # that the source repetition really "wraps around" at least once
    case pat.kind
    of nkOneOrMore:
      matches(c, pat[0], term, start,
        proc(c; term, _: Cursor): bool =
          rep(c, pat[0], term, Cursor(), then))
    of nkZeroOrMore:
      rep(c, pat[0], term, Cursor(), then)
    of nkGroup:
      proc step(c; term, start: Cursor, i: int): bool =
        if i < pat.len:
          matches(c, pat[i], term, start,
            proc(c; term, start: Cursor): bool =
              step(c, term, start, i + 1))
        else:
          then(c, term, start)
      step(c, term, start, 0)
    elif term.hasNext():
      let node = addr term.get()
      case node.kind
      of nkGroup:
        # enter the group
        matches(c, pat, Cursor(parent: addr term, node: node, pos: 0),
                start, then)
      of RepLike:
        # enter the repetition-like term, remembering the start position
        let cr = Cursor(parent: addr term, node: node, pos: node[].len - 1)
        matches(c, pat, cr, cr, then)
      else:
        matchesPattern(c, pat, node[]) and then(c, next(term), start)
    else:
      false

  proc step(c; term, start: Cursor, i: int): bool =
    if i < pat.len:
      matches(c, pat[i], term, start,
        proc(c; term, start: Cursor): bool =
          step(c, term, start, i + 1))
    else:
      # the match is only successful if all input terms were consumed
      not hasNext(term)

  step(c, Cursor(node: addr term), Cursor(), 0)

proc matchesPattern(c; pat, term: Node): bool =
  ## Tests whether the term `term` is matched by `pat`, relying only on shape
  ## and types and without binding any variables. `term` can be a pattern
  ## itself, in which case the test checks whether `pat` matches all terms
  ## that `term` would match.
  if term.kind == nkBind and term.len == 2:
    return matchesPattern(c, pat, term[1])

  case pat.kind
  of nkHole:
    true # matches everything
  of nkTrue, nkFalse:
    term.kind == pat.kind
  of nkNumber:
    term.kind == nkNumber and term.num == pat.num
  of nkSymbol, nkString:
    term.kind == pat.kind and term.sym == pat.sym
  of nkType:
    matchesType(c, pat.typ, term)
  of nkBind:
    pat.len == 1 or matchesPattern(c, pat[1], term)
  of nkConstr:
    term.kind == nkConstr and matchesList(c, pat, term)
  of nkGroup:
    # must represent a top-level list
    term.kind == nkGroup and matchesList(c, pat, term)
  else:
    unreachable()

proc matchesType(c; typ: Type, n: Node): bool =
  ## Answers the question: "does expression `n` inhabit `typ`".
  if typ.kind == tkSum:
    for it in typ.children.items:
      if matchesType(c, it, n):
        return true
    return false

  case n.kind
  of nkConstr:
    if typ.kind == tkData:
      for it in typ.constr.items:
        if matchesPattern(c, it, n):
          return true
      false
    else:
      false
  of nkTuple:
    if typ.kind == tkTuple and typ.children.len == n.len:
      for i, it in typ.children.pairs:
        if not matchesType(c, it, n[i]):
          return false
      true
    else:
      false
  of nkGroup, nkUnpack:
    unreachable()
  else:
    fitsC(c, n.typ, typ) != relNone

proc receive(c; n: NimNode, typ: Type): Node

proc typeConstr(c; n: var Node, info: NimNode, isPattern: static[bool]) =
  ## Types a construction (or construction pattern) based on the constructor's
  ## type. If that fails, an error is reported.
  template match(pat, term: Node): bool =
    # speed up matching for patterns by using a witness
    when isPattern: matchesPattern(c, pat, witness(term))
    else:           matchesPattern(c, pat, term)

  let s = c.lookup[n[0].sym]
  case s.kind
  of skConstr:
    if match(s.typ.constr[s.id], n):
      n.typ = s.typ
  of skOverload:
    var cand: seq[Type]
    for it in s.overloads.items:
      if match(it.typ.constr[it.id], n):
        cand.add it.typ
    if cand.len == 1:
      n.typ = cand[0]
    elif cand.len > 1:
      # use a type-variable in order to properly propagate the unresolved
      # type throughout the tree. The usage site is responsible for collapsing
      # the choice
      n.typ = c.newTypeVar(info, Type(kind: tkOr, children: cand))
  else:
    unreachable()

  if n.typ.isNil:
    error("no valid construction with the given shape exists", info)

proc instantiate(c; typ: Type): Type =
  ## Unwraps a ``tkForall`` type, adding its type variables to the context.
  assert typ.kind == tkForall
  var m: seq[Type]
  for i in 0..<typ.children.len-1:
    m.add c.newTypeVar(nil)

  # deep-copy all container types and update the ID of all type variables
  proc replace(typ: Type, m: seq[Type]): Type {.nimcall} =
    case typ.kind
    of tkList, tkTuple, tkFunc, tkSum:
      var t = Type(kind: typ.kind)
      for it in typ.children.items:
        t.add replace(it, m)
      t
    of tkVar:
      m[typ.id]
    else:
      typ

  replace(typ.children[^1], m)

proc numParams(typ: Type): int =
  if typ[0].kind == tkTuple:
    typ[0].children.len
  else:
    1

proc getParam(typ: Type, i: int): Type =
  if typ[0].kind == tkTuple:
    typ[0][i]
  else:
    typ[0]

proc finishUnpack(body: Node, vars: HashSet[int], info: NimNode): Node =
  ## Given the content (`body`) and the set of used list variables, produces a
  ## completed unpack expression.
  if vars.len == 0:
    error("no variables are used that can be unpacked", info)
  result = tree[Type](nkUnpack)
  for it in vars.items:
    # order doesn't matter...
    result.add tree(nkBind, Node(kind: nkVar, id: it), Node(kind: nkVar, id: it))
  result.add body
  result.typ = listT(body.typ)

proc semBindingName(c; n: NimNode, typ: Type): Node =
  ## Makes sure `n` is a valid identifier for a binding and - if so -
  ## register a new binding with the given name and `typ` with `c`.
  let name = name(n)
  if name == "_":
    # don't add a binding
    result = Node(kind: nkType, typ: typ)
  elif name in c.vars or name in c.lookup:
    error(fmt"redeclaration of {name}", n)
  else:
    let i = find(name, '_')
    if i != -1 and find(name, '_', i + 1) != -1:
      error("identifiers must only contain a single underscore", n)

    result = Node(kind: nkVar, id: c.vars.len)
    c.vars[name] = (typ, result.id)

proc toPattern(n: sink Node): Node =
  case n.kind
  of nkType: n
  of nkVar:  tree(nkBind, n)
  else:      unreachable()

proc semExpr(c; n: NimNode; inConstr, isHead=false): Node =
  ## Analyzes and type-checks expression `n`. `inConstr` tells whether within
  ## a construction, `isHead` whether the `n` is the head of a construction.
  template recurse(n: NimNode, inConstr=inConstr): untyped =
    semExpr(c, n, inConstr, false)

  case n.kind
  of nnkIdent, nnkAccQuoted:
    result = toExpr(c, resolveIdent(c, n))
    if result.kind == nkType:
      error("cannot use type here", n)
    elif result.typ.kind == tkPat and not isHead:
      result = tree(nkConstr, result)
      typeConstr(c, result, n, isPattern=false)
    elif result.typ.kind == tkForall:
      result.typ = c.instantiate(result.typ)
  of nnkIntLit:
    result = Node(kind: nkNumber, num: rational(n.intVal.int),
                  typ: c.lookup["z"].typ)
  of nnkFloatLit:
    result = Node(kind: nkNumber, num: rational(n.floatVal),
                  typ: c.lookup["r"].typ)
  of nnkStrLit:
    result = Node(kind: nkString, sym: n.strVal, typ: c.lookup["string"].typ)
  of nnkPar:
    result = recurse(n[0])
  of nnkTupleConstr:
    n.expectMinLen 1
    var tup = Node(kind: nkTuple, typ: Type(kind: tkTuple))
    for it in n.items:
      let x = recurse(it)
      tup.typ.add x.typ
      tup.add x
    result = tup
  of nnkObjConstr:
    var rec = Node(kind: nkRecord)
    var s = resolveIdent(c, n[0])
    if s.kind != skType or s.typ.kind != tkRecord:
      error("must be the name of a record type", n[0])
    rec.typ = s.typ
    for i in 1..<n.len:
      let it = n[i]
      let name = name(it[0])
      it.expectKind nnkExprColonExpr
      block search:
        for x in rec.typ.fields.items:
          if x.name == name:
            let x = receive(c, it[1], x.typ)
            rec.add tree(nkAssoc, Node(kind: nkSymbol, sym: name), x)
            break search
        error(fmt"record has no field of name {name}", it[0])
    result = rec
  of nnkCallKinds:
    if n.kind == nnkPrefix and n[0].eqIdent("..."):
      c.unpacked.add initHashSet[int](0) # push an unpack context
      let body = recurse(n[1], false) # analyze the body
      let vars = c.unpacked.pop() # pop the context again
      return finishUnpack(body, vars, n)

    let callee = semExpr(c, n[0], false, isHead=true)
    var call: Node
    var sig: Type
    if callee.typ.kind == tkVar:
      # try to infer the type as a function type
      let t = skip(c, callee.typ)
      if c.tvars[t.id].curr.kind == tkFunc:
        sig = c.tvars[t.id].curr
      elif c.tvars[t.id].limit.kind == tkFunc:
        sig = c.tvars[t.id].limit
        c.tvars[t.id].curr = sig
      else:
        error("cannot infer as being of function type", n[0])
    else:
      sig = callee.typ

    var isConstr = false
    if callee.kind == nkSymbol:
      # must be a construction expression, which is typed based on shape
      call = Node(kind: nkConstr)
      call.add callee
      isConstr = true
    elif sig.kind == tkFunc:
      call = Node(kind: nkCall)
      call.add callee
      let expect = numParams(sig)
      if n.len - 1 > expect:
        error(fmt"expected {expect} arguments, but got {n.len - 1}", n)
    else:
      error(fmt"expected something callable, got '{sig}'", n)

    if callee.kind == nkRelation:
      for it in c.relations[callee.id].params.items:
        if not it.input:
          error("relations that bind are only allowed in a 'premise'", n)

    for i in 1..<n.len:
      let x = recurse(n[i], isConstr)
      # function applications are type-checked right away
      if sig.kind == tkFunc:
        check(c, getParam(sig, i - 1), x.typ, n[i])
      call.add x

    if callee.kind == nkSymbol:
      if not inConstr:
        typeConstr(c, call, n, isPattern=false)
      # else: only start typing from the top-level construction expression
      result = call
    else:
      # typed directly
      call.typ = sig[1]
      result = call
  of nnkBracketExpr:
    let a = recurse(n[0])
    if a.typ.kind == tkList:
      let b = receive(c, n[1], c.lookup["z"].typ)
      # apply the list to an integer value (an index)
      result = tree(nkCall, a, b)
      result.typ = a.typ[0]
    else:
      # it's the plug operation
      let b = recurse(n[1])
      result = tree(nkPlug, a, b)
      # inherit from the argument, even if not entirely correct
      result.typ = b.typ
  of nnkDotExpr:
    let a = recurse(n[0])
    if a.typ.kind != tkRecord:
      error("must be a record type", n[0])
    for it in a.typ.fields.items:
      if it.name == name(n[1]):
        result = tree(nkProject, a, Node(kind: nkSymbol, sym: it.name))
        result.typ = it.typ
        return
    error(fmt"record has no field of name: {name(n[1])}", n[1])
  of nnkCurly:
    n.expectMinLen 1
    result = Node(kind: nkSet)
    let typ = c.newTypeVar(n)
    for it in n.items:
      let term = recurse(it)
      check(c, typ, term.typ, it)
      result.add term
    # typed as a map from the set element to a boolean
    result.typ = fntype(typ, Type(kind: tkBool))
  of nnkTableConstr:
    n.expectMinLen 1
    result = Node(kind: nkMap)
    # both the key and value type are inferred from usage
    let key = c.newTypeVar(n)
    let val = c.newTypeVar(n)
    for it in n.items:
      it.expectKind nnkExprColonExpr
      let k = recurse(it[0])
      check(c, key, k.typ, it[0])
      let v = recurse(it[1])
      check(c, val, v.typ, it[1])
      result.add tree(nkAssoc, k, v)
    result.typ = fntype(key, val)
  of nnkStmtList, nnkStmtListExpr:
    n.expectLen 1
    result = recurse(n[0])
  of nnkForStmt:
    n.expectLen 3
    let frm = recurse(n[1])
    if frm.typ.kind != tkList:
      error(fmt"expected list type, but got {frm.typ}", n[1])
    let to = c.semBindingName(n[0], frm.typ[0])
    if to.kind == nkType:
      error("discard underscore not allowed in this context", n[0])
    let body = recurse(n[2])
    result = tree(nkUnpack, tree(nkBind, to, frm), body)
    result.typ = listT(body.typ)
    c.vars.del(name(n[0]))
  else:
    error("invalid expression", n)

proc receive(c; n: NimNode, typ: Type): Node =
  result = semExpr(c, n)
  check(c, typ, result.typ, n)

proc semPatternIdent(c; n: NimNode, accept: set[NodeKind]): Node =
  ## Resolves an identifier appearing in a pattern.
  case n.kind
  of nnkIdent:
    var name = n.strVal
    if name == "_":
      return Node(kind: nkType, typ: Type(kind: tkAll))

    let sub = name.find('_')
    if sub != -1:
      name = substr(name, 0, sub-1)

    if n.strVal in c.vars:
      error("cannot use bound variable identifier in pattern", n)
    elif name in c.lookup:
      result = toExpr(c, c.lookup[name])
      if result.kind == nkSymbol:
        result = tree(nkConstr, result) # auto-expand
      elif result.kind notin {nkContext, nkHole, nkType, nkTrue, nkFalse}:
        error("only contexts, values, and types may be used as a pattern", n)

      if result.kind notin accept:
        error("entity not allowed in this context", n)

      if sub != -1:
        # create a binding
        if name == "any":
          # infer type from usage
          result.typ = c.newTypeVar(n)
        elif result.kind notin {nkType, nkContext}:
          error("captures may only use types and contexts", n)
        elif nkVar notin accept:
          error("captures are not allowed in this context", n)

        let id = c.vars.len # a unique ID (within the current scope)
        var typ = result.typ
        if c.depth > 0:
          # the actual type of the variable is a list, but the type of the
          # pattern is the unwrapped type
          var temp = result.typ
          for _ in 0..<c.depth:
            temp = listT(temp)

          c.vars[n.strVal] = (temp, id)
        else:
          c.vars[n.strVal] = (typ, id)

        if result.kind == nkContext:
          result = tree(nkBind, Node(kind: nkVar, id: id), result)
        else:
          result = tree(nkBind, Node(kind: nkVar, id: id), Node(kind: nkType, typ: typ))
        result.typ = typ
    else:
      error("undeclared identfier: " & name, n)
  of nnkAccQuoted:
    n.expectLen 1
    result = semPatternIdent(c, n[0], accept)
  else:
    error("expected identifier", n)

proc semPattern(c; n: NimNode; accept: set[NodeKind], check = true): Node =
  ## Analyzes the pattern expression `n`. `check` controls whether
  ## construction patterns are typed right away.
  template recurse(n: NimNode, accept: set[NodeKind]): Node =
    semPattern(c, n, accept, check)

  template require(kind: NodeKind, msg: string) =
    if kind notin accept:
      error(msg, n)

  # note: the type of a pattern says what terms it matches
  case n.kind
  of nnkIdent, nnkAccQuoted:
    result = semPatternIdent(c, n, accept)
    if result.kind == nkConstr and check:
      typeConstr(c, result, n, isPattern=true)
  of nnkIntLit:
    require(nkNumber, "number not allowed in this context")
    result = Node(kind: nkNumber, num: rational(n.intVal.int),
                  typ: c.lookup["z"].typ)
  of nnkStrLit:
    require(nkString, "string not allowed in this context")
    result = Node(kind: nkString, sym: n.strVal,
                  typ: c.lookup["string"].typ)
  of nnkPar:
    # only used for modifying associativity and precedence, skip
    result = recurse(n[0], accept)
  of nnkBracketExpr:
    # an r-pattern-based decomposition
    n.expectLen 2
    require(nkPlug, "decomposition not allowed in this context")
    let p = semPatternIdent(c, n[0], accept * {nkVar} + {nkContext})
    let arg = semPattern(c, n[1], accept - {nkGroup, nkOneOrMore, nkZeroOrMore})
    result = tree(nkPlug, p, arg)
    result.typ = arg.typ
    # problem: the type of context is dependent upon the plugged-with
    # pattern (and its own structure)... This is not really supported by the
    # type system, so we use argument's type, which is a good approximation
  of nnkPrefix:
    n.expectLen 2
    let naccept = accept - {nkZeroOrMore, nkOneOrMore, nkPlug} + {nkGroup}
    if n[0].eqIdent("+"):
      inc c.depth
      require(nkOneOrMore, "repetition not allowed in this context")
      result = tree(nkOneOrMore, recurse(n[1], naccept))
      dec c.depth
    elif n[0].eqIdent("*"):
      inc c.depth
      require(nkZeroOrMore, "repetition not allowed in this context")
      result = tree(nkZeroOrMore, recurse(n[1], naccept))
      dec c.depth
    elif n[0].eqIdent("..."):
      error("unpacking is not allowed in a pattern", n)
    else:
      error("unknown prefix", n)
    # only assign a type when the element has one
    if result[0].typ != nil:
      result.typ = listT(result[0].typ)
  of nnkBracket:
    n.expectMinLen 1
    require(nkGroup, "group not allowed in this context")
    result = Node(kind: nkGroup)
    for it in n.items:
      result.add recurse(it, accept - {nkGroup})
    # groups have no type because they're special-cased by the matcher
  of nnkTupleConstr:
    n.expectMinLen 1
    require(nkTuple, "tuple not allowed in this context")
    result = Node(kind: nkTuple, typ: Type(kind: tkTuple))
    let accept = accept - {nkOneOrMore, nkZeroOrMore, nkGroup} + InTuplePat
    for it in n.items:
      let e = semPattern(c, it, accept, check=true)
      result.typ.add e.typ
      result.add e
  of nnkCall:
    require(nkConstr, "construction not allowed in this context")
    result = Node(kind: nkConstr)
    result.add Node(kind: nkSymbol, sym: name(n[0]))
    let accept = accept + InConstrPat
    for i in 1..<n.len:
      result.add semPattern(c, n[i], accept, check=false)
    if check:
      typeConstr(c, result, n, isPattern=false)
  else:
    error("not a valid pattern expression", n)

proc semPattern(c; n: NimNode, accept: set[NodeKind], typ: Type): Node =
  ## Analyzes a pattern and makes sure it only matches terms part of `typ`.
  result = semPattern(c, n, accept, check=false)
  if not matchesType(c, typ, witness(result)):
    error(fmt"pattern matches constructions not belonging to {typ}", n)

proc checkRPattern(n: Node, info: NimNode) =
  ## Makes sure the R-pattern item `n` is valid, reporting an error if not.
  var foundHole = false
  proc aux(n: Node) =
    case n.kind
    of nkHole, nkContext:
      if foundHole:
        error("pattern must contain only one hole", info)
      foundHole = true
    of nkFail, nkTrue, nkFalse, nkSymbol, nkNumber, nkString, nkFunc,
       nkRelation, nkType, nkVar:
      discard "nothing to do"
    of withChildren:
      for it in n.children.items:
        aux(it)

  aux(n)
  if not foundHole:
    error("pattern is missing a hole", info)

proc semPremise(c; n: NimNode): Node =
  var n = n
  # premises may be wrapped in an ellipsis, which designates them as being
  # repeated
  let e = ellipsis(n)
  var unpack = false
  if e != nil:
    n = e
    unpack = true
  if n.kind == nnkPar:
    n = n[0]

  n.expectKind nnkCallKinds
  n[0].expectKind nnkIdent
  if n[0].strVal in c.lookup:
    let s {.cursor.} = c.lookup[n[0].strVal]
    if s.kind == skRelation:
      n.expectLen 1 + c.relations[s.id].params.len
      var res = Node(kind: nkCall)
      res.add Node(kind: nkRelation, id: s.id, typ: s.typ)
      var accept = AllPat
      if unpack:
        accept = accept - {nkPlug}
        c.unpacked.add initHashSet[int](0)
        inc c.depth
      for i, param in c.relations[s.id].params.pairs:
        if param.input:
          res.add receive(c, n[i + 1], param.typ)
        else:
          res.add semPattern(c, n[i + 1], accept, param.typ)
      res.typ = s.typ[1]
      if unpack:
        dec c.depth
        result = finishUnpack(res, c.unpacked.pop(), n)
      else:
        result = res
    else:
      error("expected name of relation", n[0])
  else:
    error("undeclared identifier", n[0])

proc semPredicate(c; n: NimNode): Node =
  if n[0].eqIdent("premise"):
    n.expectLen 2
    semPremise(c, n[1])
  elif n[0].eqIdent("where"):
    # it'd be much nicer if `where x, y` could be written as `let x = y`,
    # but that syntax doesn't work for more complex pattern matching
    n.expectLen 3
    let pat = semPattern(c, n[1], AllPat)
    tree(nkMatches, pat, receive(c, n[2], pat.typ))
  elif n[0].eqIdent("condition"):
    n.expectLen 2
    let term = semExpr(c, n[1])
    if term.typ.kind == tkList:
      check(c, c.lookup["bool"].typ, term.typ[0], n[1])
    else:
      check(c, c.lookup["bool"].typ, term.typ, n[1])
    term
  else:
    error("expected where/condition", n)
    unreachable()

proc semLet(c; n: NimNode): Node =
  ## Analyses and a ``let`` statement, transforming it into a ``nkMatches``
  ## expression.
  n.expectLen 1
  let def = n[0]
  def.expectKind {nnkIdentDefs, nnkVarTuple}
  let e = semExpr(c, def[^1])

  var pat: Node
  case def.kind
  of nnkIdentDefs:
    # a single identifier binding is introduced
    def.expectLen 3
    def[1].expectKind nnkEmpty
    pat = toPattern c.semBindingName(def[0], e.typ)
  of nnkVarTuple:
    # tuple unpacking + identifier binding
    pat = Node(kind: nkTuple)
    if e.typ.kind != tkTuple:
      error("expression must be of tuple type", def[^1])
    elif (let L = e.typ.children.len; L != def.len - 2):
      error(fmt"expected tuple with {def.len-2} elements, but got {L}",
            def[^1])

    for i in 0..<def.len-2:
      pat.add toPattern(c.semBindingName(def[i], e.typ[i]))
  else:
    unreachable()

  tree(nkMatches, pat, e)

proc semRelation(c; n: NimNode, rel: var Relation[Type], id: int) =
  ## Parses and verifies the body of a relation.
  let body = n[2]
  body.expectKind nnkStmtList
  for it in body.items:
    case it.kind
    of nnkCallKinds:
      var predicates: seq[Node]
      var conclusion = newSeq[Node](rel.params.len + 1)
      conclusion[0] = Node(kind: nkRelation, id: id)
      case it[0].strVal
      of "axiom":
        it.expectLen 2 + rel.params.len
        it[1].expectKind nnkStrLit
        for i in 2..<it.len:
          if rel.params[i - 2].input:
            # inputs must be patterns
            conclusion[i - 1] = semPattern(c, it[i], AllPat,
                                           rel.params[i - 2].typ)
          else:
            # outputs must be terms
            conclusion[i - 1] = receive(c, it[i], rel.params[i - 2].typ)
      of "rule":
        it.expectLen 3
        it[1].expectKind nnkStrLit

        # processing needs to happen in the correct order, so that the
        # variables are available when needed by premise/where/condition
        # clauses. Process the conclusion input patterns first, as they can
        # bind variables
        for x in it[2].items:
          if x.kind in nnkCallKinds and x[0].eqIdent("conclusion"):
            x.expectLen 1 + rel.params.len
            for i in 1..<x.len:
              if rel.params[i - 1].input:
                conclusion[i] = semPattern(c, x[i], AllPat,
                                           rel.params[i - 1].typ)
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
                if not rel.params[i - 1].input:
                  # outputs must be terms
                  conclusion[i] = receive(c, x[i], rel.params[i - 1].typ)
            else:
              predicates.add semPredicate(c, x)
          of nnkLetSection:
            predicates.add semLet(c, x)
          of nnkCommentStmt:
            discard # TODO: implement
          else:
            error("expected call syntax or comment", x)

        if not hasConclusion:
          error("rule is missing a conclusion", it)
      else:
        error("expected axiom or rule", it)

      # build the final chain of implications:
      var e = Node(kind: nkCall, children: conclusion)
      for i in countdown(predicates.high, 0):
        e = tree(nkImplies, predicates[i], e)

      c.finalize(e)
      c.flushVars()
      rel.rules.add Rule[Type](name: it[1].strVal, body: e)
    of nnkCommentStmt:
      discard # TODO: implement
    else:
      error("expected declaration or comment", it)

proc parseTypeUse(c: Context; n: NimNode): Type

proc parseFuncType(c: Context; n: NimNode): Type =
  n.expectKind nnkInfix
  n.expectLen 3
  Type(kind: tkFunc,
        children: @[parseTypeUse(c, n[1]), parseTypeUse(c, n[2])])

proc sum(a, b: Type): Type =
  ## Creates a sum type from `a` and `b`.
  result = Type(kind: tkSum)
  if a.kind == tkSum:
    result.children.add a.children
  else:
    result.add a

  var c = Context() # create a dummy context for the type relations
  var i = 0
  block add:
    while i < result.children.len:
      if fits(c, b, result[i]) in {relEqual, relSubtype}:
        break add # `b` is already part of the sum
      elif fits(c, result[i], b) == relSubtype:
        # the sum element is part of `b`. Remove it because it's now redundant
        result.children.del(i)
      else:
        inc i

    result.add b

  if result.children.len == 1:
    result = result[0] # normalize

proc parseTypeUse(c: Context; n: NimNode): Type =
  case n.kind
  of nnkInfix:
    if n[0].eqIdent("->"):
      # it's a function type
      parseFuncType(c, n)
    elif n[0].eqIdent("+"):
      # it's a sum type
      sum(parseTypeUse(c, n[1]), parseTypeUse(c, n[2]))
    else:
      error("not a type use", n)
      unreachable()
  of nnkPrefix:
    if n[0].eqIdent("*"):
      listT(parseTypeUse(c, n[1]))
    else:
      error("not a type use", n)
      unreachable()
  of nnkIdent, nnkAccQuoted:
    let s = resolveIdent(c, n)
    if s.kind == skType:
      s.typ
    else:
      error("expected a type", n)
      unreachable()
  of nnkTupleConstr:
    var r = Type(kind: tkTuple)
    for it in n.items:
      r.add parseTypeUse(c, it)
    r
  of nnkPar:
    n.expectLen 1
    parseTypeUse(c, n[0])
  else:
    error("not a type use", n)
    unreachable()

proc semConstrDef(c; n: NimNode, typ: Type): Node =
  ## Parses a constructor definition, which use a subset of the available
  ## pattern syntax.
  case n.kind
  of nnkIdent, nnkAccQuoted:
    # turn into a tree to make downstream processing easier
    result = Node(kind: nkSymbol, sym: name(n), typ: Type(kind: tkPat))
    result = tree(nkConstr, result)
    result.typ = typ
  of nnkCall:
    proc addChecked(r: var Node, n: sink Node, info: NimNode) {.nimcall.} =
      if r.len > 0 and r.children[^1].kind in {nkOneOrMore, nkZeroOrMore} and
         n.kind in {nkOneOrMore, nkZeroOrMore}:
        error("repetition must not be followed by repetition", info)
      r.add n

    proc semConstrSub(c; n: NimNode): Node {.nimcall.} =
      case n.kind
      of nnkIdent, nnkAccQuoted:
        let s = resolveIdent(c, n)
        result = toExpr(c, s)
        if result.kind == nkSymbol:
          result = tree(nkConstr, result) # auto-expand
        elif result.kind != nkType:
          error("expected type or constructor name", n)
      of nnkPrefix:
        if n[0].eqIdent("*"):
          result = tree(nkZeroOrMore, semConstrSub(c, n[1]))
        elif n[0].eqIdent("+"):
          result = tree(nkOneOrMore, semConstrSub(c, n[1]))
        else:
          error("unknown prefix", n)
      of nnkBracket:
        n.expectMinLen 1
        result = Node(kind: nkGroup)
        for it in n.items:
          result.addChecked(semConstrSub(c, it), it)
      of nnkCall:
        result = tree(nkConstr, Node(kind: nkSymbol, sym: name(n[0])))
        for i in 1..<n.len:
          result.addChecked(semConstrSub(c, n[i]), n[i])
      else:
        error("expected identifier or call syntax", n)

    result = semConstrSub(c, n)
    result[0].typ = Type(kind: tkPat)
    result.typ = typ
  else:
    error("expected identifier or call syntax", n)

proc semType(c; body: NimNode, self: Type; base = Type(nil)) =
  ## Analyzes the body of an inductive type definition `body`. `self` is the
  ## type to add the constructions to. If `base` is non-nil, makes sure that
  ## `self` is a subtype of `base`.
  body.expectKind nnkStmtList

  if base != nil:
    # presume that the type is a subtype of the specified base, so that
    # constructions involving self-recursion work
    c.typerelCache[(self, base)] = relSubtype

  for it in body.items:
    let pat = semConstrDef(c, it, self)

    # make sure there's no equivalent pattern in the current type:
    for p in self.constr.items:
      if matchesPattern(c, p, pat) and matchesPattern(c, pat, p):
        error("duplicate construction pattern", it)

    if base != nil and not matchesType(c, base, pat):
      error("construction is not covered by the parent type", it)

    self.constr.add pat
    # add the constructor symbol to the lookup table:
    let
      name = pat[0].sym
      sym = Sym(kind: skConstr, id: self.constr.high, typ: self)
    c.lookup.withValue name, prev:
      if prev.kind == skConstr:
        prev[] = Sym(kind: skOverload, overloads: @[move prev[], sym])
      elif prev.kind == skOverload:
        prev.overloads.add sym
      else:
        error(fmt"{name} cannot be overloaded", it)
    do:
      c.lookup[name] = sym

proc semBody(c; n: NimNode, typ: Type, top: bool): Node

proc restore(c; start: int) =
  # collect the names of the vars to remove:
  var names: seq[string]
  for k, v in c.vars.pairs:
    if v.id >= start:
      names.add k
  # then remove the vars:
  for it in names.items:
    c.vars.del(it)

proc semScopedBody(c; n: NimNode, typ: Type): Node =
  var start = c.vars.len
  result = semBody(c, n, typ, false)
  c.restore(start)

proc semCase(c; n: NimNode, typ: Type): Node =
  ## Analyzes and type-checks a ``case`` expression.
  result = tree(nkMatch, semExpr(c, n[0]))
  let input = result[0].typ

  for i in 1..<n.len:
    let b = n[i]
    var o: Node
    var start = c.vars.len
    case b.kind
    of nnkOfBranch:
      let len = b.len - 1
      if input.kind != tkTuple and len > 1:
        error(fmt"expected 1 pattern, got {len}", b)
      elif input.kind == tkTuple and len > input.children.len:
        error(fmt"expected {input.children.len} pattern(s), got {len}", b)

      o = tree[Type](nkOf)
      for i in 0..<len:
        # the parameter's type must be equal to or a subtype of what the
        # pattern matches
        let dest = if input.kind != tkTuple: input else: input[i]
        var p = semPattern(c, b[i], OfBranchPat)
        if p.kind == nkGroup:
          # the pattern is really a list pattern...
          if dest.kind != tkList:
            error(fmt"destination is a '{dest}', not a list", b[i])

          for it in p.children.items:
            if it.kind in {nkZeroOrMore, nkOneOrMore}:
              check(c, it.typ, dest, b[i])
            else:
              check(c, it.typ, dest[0], b[i])
        else:
          check(c, p.typ, dest, b[i])
        o.add p
    of nnkElse, nnkElseExpr:
      # turn into a "match all" branch
      o = tree(nkOf, Node(kind: nkType, typ: Type(kind: tkAll)))
    else:
      error("expected 'else' or 'of' branch", b)

    o.add semBody(c, b[^1], typ, false)
    result.add o
    # branches introduce a new scope:
    c.restore(start)

proc semBody(c; n: NimNode, typ: Type, top: bool): Node =
  ## Analyzes a tree appearing somwhere nested in a function body. `typ` is
  ## the expected expression's expected type, and `top` signals whether it's a
  ## top-level expression the type of the implicit.
  case n.kind
  of nnkStmtList:
    var stmts: seq[Node]
    # skip leading comments:
    var start = 0
    while top and start < n.len and n[start].kind == nnkCommentStmt:
      inc start
    # process the leading 'let' statements:
    for i in start..<n.len-1:
      if n[i].kind == nnkLetSection:
        stmts.add semLet(c, n[i])
      else:
        error("expected 'let' statement", n[i])
    result = semBody(c, n[^1], typ, top)
    if stmts.len > 0:
      # lower the let statements into nested match expressions
      for i in countdown(stmts.high, 0):
        result = tree(nkMatch, stmts[i][1], tree(nkOf, stmts[i][0], result))
  of nnkCaseStmt:
    result = semCase(c, n, typ)
  of nnkIfStmt, nnkIfExpr:
    if n.len > 1 and n[1].kind == nnkElifBranch:
      error("only if/else is supported", n[1])
    let cond = semExpr(c, n[0][0])
    if cond.kind == nkUnpack:
      # special case: unpack expressions are allowed as conditions
      if cond.typ[0].kind != tkBool:
        error(fmt"expected bool type, got {cond.typ[0]}", n[0][0])
    elif cond.typ.kind != tkBool:
      error(fmt"expected bool type, got {cond.typ}", n[0][0])
    let els =
      if n.len == 1: c.lookup["fail"].e
      else:          semScopedBody(c, n[1][0], typ)
    result = tree(nkIf, cond, semScopedBody(c, n[0][1], typ), els)
    result.typ = typ
  else:
    # must be a normal term
    result = receive(c, n, typ)

proc semFunctionHeader(c; params: NimNode): Type =
  ## Constructs the function type using the parameter list.
  params.expectKind nnkFormalParams
  if params.len == 1:
    error("functions must have at least one parameter", params)

  var args: seq[Type]
  # check and gather the parameters first:
  for i in 1..<params.len:
    let def = params[i]
    def.expectKind nnkIdentDefs
    if def[^1].kind != nnkEmpty:
      error("default values are disallowed", def[^1])
    # no parameter type is interpreted as meaning "accepts everything"
    let typ =
      if def[^2].kind == nnkEmpty:
        Type(kind: tkAll)
      else:
        parseTypeUse(c, def[^2])

    # the names are validated later, when registering the bindings
    for _ in 0..<def.len-2:
      args.add typ

  # then assemble and return the function type:
  if args.len == 1:
    fntype(args[0], parseTypeUse(c, params[0]))
  else:
    fntype(tup(args), parseTypeUse(c, params[0]))

proc semFunction(c; def: NimNode, sig: Type): Function[Type] =
  ## Analyzes and type-checks function definition `def`, producing the fully-
  ## typed definition.
  result = Function[Type](name: name(macros.name(def)))
  let
    body   = def.body
    params = def.params

  if body.kind == nnkEmpty:
    # empty function; this is currently allowed
    result.body = Node(kind: nkHole)
    return

  # register the bindings for all parameters:
  var branch = Node(kind: nkOf)
  var paramIdx = 0
  for i in 1..<params.len:
    for j in 0..<params[i].len-2: # go over all identifiers
      branch.add:
        toPattern c.semBindingName(params[i][j], getParam(sig, paramIdx))
      inc paramIdx

  branch.add semBody(c, body, sig[1], top=true)
  result.body = tree(nkMatch, Node(kind: nkHole), branch)
  c.finalize(result.body)
  c.flushVars()

proc semRelationHeader(c; n: NimNode): Relation[Type] =
  ## Parses and checks the relation's signature from `n`.
  n.expectLen 3
  n[1].expectKind nnkCallKinds

  result = Relation[Type](name: name(n[1][0]))
  # parse the input/output specification:
  for i in 1..<n[1].len:
    case n[1][i].kind
    of nnkCommand:
      # cannot use 'in', because that's a special token only usable as an
      # infix :(
      n[1][i].expectLen 2
      if n[1][i][0].eqIdent("inp"):
        result.params.add (true, parseTypeUse(c, n[1][i][1]))
      else:
        error("expected either 'inp' or 'out'", n[1][i])
    of nnkMutableTy:
      # 'out' is parsed as ``nnkMutableTy``
      n[1][i].expectLen 1
      result.params.add (false, parseTypeUse(c, n[1][i][0]))
    else:
      error("expected either 'inp x' or 'out x'", n[1][i])

proc convertFrom[T, U](to: var T, x: sink U,
                       map: var Table[Type, types.TypeId],
                       types: var seq[types.Type]) =
  ## Convenience procedure for converting structs using the ref-based
  ## types representation to an equivalent struct using the ID-based type
  ## representation.
  mixin convertFrom
  when T is U:
    to = x
  when T is (object | tuple):
    for field1, a in fieldPairs(to):
      for field2, b in fieldPairs(x):
        when field1 == field2:
          when typeof(b) is TypeKind:
            a = typeof(a)(b.ord)
          elif field1 == "kind":
            a = b # discriminator assignment
          else:
            convertFrom(a, b, map, types)
  elif T is seq:
    to.newSeq(x.len)
    for i in 0..<x.len:
      convertFrom(to[i], x[i], map, types)
  else:
    to = x

proc convertFrom(to: var types.TypeId, x: sink Type,
                 map: var Table[Type, types.TypeId],
                 types: var seq[TType]) =
  ## The interesting part of the conversion logic.
  if x.isNil or x.kind == tkPat:
    # pat types are only needed for the type checker; they're discarded here
    to = 0
  else:
    let id = map.mgetOrPut(x, types.len)
    if id == types.len: # new mapping?
      # reserve a slot before recursing, so that recursive types work
      types.add default(TType)
      var c: TType
      convertFrom(c, x[], map, types)
      types[id] = c
    to = id + 1

proc sem(body: NimNode): LangDef =
  ## The entry point into the semantic checker.
  body.expectKind nnkStmtList

  var
    c = Context()
  let
    boolType = Type(kind: tkBool)
    intType = Type(kind: tkInt)
    ratType = Type(kind: tkRat)

  # add the built-in symbols:
  c.lookup["any"] = Sym(kind: skType, typ: Type(kind: tkAll))
  c.lookup["z"] = Sym(kind: skType, typ: intType)
  c.lookup["r"] = Sym(kind: skType, typ: ratType)
  c.lookup["bool"] = Sym(kind: skType, typ: boolType)
  # a string is a list of UTF-32 bytes
  c.lookup["string"] = Sym(kind: skType, typ: listT(intType))
  c.lookup["true"] = Sym(kind: skDef, e: Node(kind: nkTrue, typ: boolType))
  c.lookup["false"] = Sym(kind: skDef, e: Node(kind: nkFalse, typ: boolType))
  c.lookup["hole"] = Sym(kind: skDef, e: Node(kind: nkHole, typ: Type(kind: tkVoid)))
  c.lookup["fail"] = Sym(kind: skDef, e: Node(kind: nkFail, typ: Type(kind: tkVoid)))

  proc builtin(c; name: string, typ: Type) {.nimcall.} =
    ## Adds a built-in function with the given name and type.
    c.functions.add Function[Type](name: name, body: Node(kind: nkHole))
    c.lookup[name] = Sym(kind: skFunc, id: c.functions.high, typ: typ)

  c.builtin("or", fntype(tup(boolType, boolType), boolType))
  c.builtin("and", fntype(tup(boolType, boolType), boolType))
  c.builtin("in", forall(2, fntype(tup(tvar(0), tvar(1)), boolType)))
  c.builtin("notin", forall(2, fntype(tup(tvar(0), tvar(1)), boolType)))
  c.builtin("same", forall(1, fntype(tup(tvar(0), tvar(0)), boolType)))
  c.builtin("len", forall(1, fntype(listT(tvar(0)), intType)))
  c.builtin("zip", forall(2, fntype(tup(listT(tvar(0)), listT(tvar(1))), listT(tup(tvar(0), tvar(1))))))
  c.builtin("set", forall(1, fntype(listT(tvar(0)), fntype(tvar(0), boolType))))
  c.builtin("map", forall(2, fntype(listT(tup(tvar(0), tvar(1))), fntype(tvar(0), tvar(1)))))
  c.builtin("neg", forall(1, fntype(tvar(0), tvar(0))))
  c.builtin("+", forall(1, fntype(tup(tvar(0), tvar(0)), tvar(0))))
  c.builtin("-", forall(1, fntype(tup(tvar(0), tvar(0)), tvar(0))))
  c.builtin("<=", forall(1, fntype(tup(ratType, ratType), boolType)))
  c.builtin("<", forall(1, fntype(tup(ratType, ratType), boolType)))
  c.builtin("/", forall(1, fntype(tup(ratType, ratType), ratType)))
  c.builtin("^", forall(1, fntype(tup(tvar(0), intType), tvar(0))))
  c.builtin("*", forall(1, fntype(tup(tvar(0), tvar(0)), tvar(0))))

  # first pass: make sure the broad shape of `body` is correct and collect the
  # names of all symbols while looking for and reporting collisions
  for it in body.items:
    case it.kind
    of nnkCallKinds:
      it[0].expectKind nnkIdent
      case it[0].strVal
      of "inductive":
        it.expectLen 3
        addSym(c, name(it[1][0]), it):
          Sym(kind: skRelation, id: c.relations.len)
        c.relations.add Relation[Type](name: name(it[1][0]))
      of "typ":
        it.expectLen 3
        addSym(c, name(it[1]), it):
          Sym(kind: skType, typ: Type(kind: tkData))
      of "subtype":
        it.expectLen 4
        addSym(c, name(it[1]), it):
          Sym(kind: skType, typ: Type(kind: tkData))
      of "context":
        it.expectLen 3
        # use void as the type, so that an r-pattern can be used everywhere
        addSym(c, name(it[1]), it):
          Sym(kind: skContext, id: c.matchers.len, typ: Type(kind: tkVoid))
        c.matchers.add Pattern[Type](name: name(it[1]))
      of "record":
        it.expectLen 3
        addSym(c, name(it[1]), it):
          Sym(kind: skType, typ: Type(kind: tkRecord))
      of "alias":
        it.expectLen 3
        let sym = c.resolveIdent(it[2])
        addSym(c, name(it[1]), it): sym
      of "def":
        it.expectLen 3
        addSym(c, name(it[1]), it):
          Sym(kind: skDef, e: semExpr(c, it[2]))
      else:
        error(fmt"unknown declaration: '{it[0].strVal}'", it)
    of nnkFuncDef:
      addSym(c, name(macros.name(it)), it):
        Sym(kind: skFunc, id: c.functions.len)
      # only add a placeholder for now; it's replaced with a proper entry later
      c.functions.add Function[Type]()
    of nnkCommentStmt:
      # TODO: process
      discard
    else:
      error("expected declaration, function, or doc comment", it)

  # second pass: process all type definitions, plus the signatures
  # of functions and relations
  for it in body.items:
    case it.kind
    of nnkCallKinds:
      case it[0].strVal
      of "inductive":
        let rel = semRelationHeader(c, it)
        let s = c.lookup[rel.name]
        var params = Type(kind: tkTuple)
        for it in rel.params.items:
          params.add it.typ

        s.typ = fntype(params, boolType)
        c.relations[s.id] = rel
      of "typ":
        semType(c, it[2], c.lookup[name(it[1])].typ)
      of "subtype":
        let base = parseTypeUse(c, it[2])
        semType(c, it[3], c.lookup[name(it[1])].typ, base)
      of "record":
        let typ = c.lookup[name(it[1])].typ
        it[2].expectMinLen 1
        for ece in it[2].items:
          ece.expectKind nnkExprColonExpr
          let name = ece[0].strVal
          for f in typ.fields.items:
            if f.name == name:
              error(fmt"field with name '{name}' already exists", ece[0])
          typ.fields.add (name, parseTypeUse(c, ece[1]))
    of nnkFuncDef:
      c.lookup[name(macros.name(it))].typ = semFunctionHeader(c, it.params)
    else:
      discard "nothing to do"

  # third pass: process the remaining declarations
  for it in body.items:
    case it.kind
    of nnkCallKinds:
      case it[0].strVal
      of "inductive":
        let id = c.lookup[name(it[1][0])].id
        semRelation(c, it, c.relations[id], id)
      of "context":
        let id = c.lookup[name(it[1])].id
        it[2].expectKind nnkStmtList
        for x in it[2].items:
          var pat = semPattern(c, x, {nkContext, nkHole, nkConstr})
          checkRPattern(pat, x)
          c.finalize(pat) # resolve type variables
          c.flushVars()
          c.matchers[id].patterns.add pat
    of nnkFuncDef:
      c.lookup.withValue name(macros.name(it)), val:
        c.functions[val.id] = semFunction(c, it, val.typ)
    else:
      discard "nothing to do"

  # convert the internal representation to the external one and return it
  var
    lang = LangDef()
    map = initTable[Type, types.TypeId]()
  lang.functions.convertFrom(c.functions, map, lang.types)
  lang.relations.convertFrom(c.relations, map, lang.types)
  lang.matchers.convertFrom(c.matchers, map, lang.types)

  # populate the names table:
  for name, sym in c.lookup.pairs:
    if sym.kind == skType:
      var id: types.TypeId
      convertFrom(id, sym.typ, map, lang.types)
      lang.names[id] = name

  result = lang

proc removeQuoted(n: NimNode): NimNode =
  ## Replaces all accent-quoted identifiers with raw identifiers.
  if n.kind == nnkAccQuoted and n.len == 1:
    result = n[0] # remove the quote
  else:
    result = n
    for i in 0..<n.len:
      result[i] = removeQuoted(n[i])

macro language*(body: untyped): LangDef =
  ## Parses and type-checks the meta-language module `body` and returns it as
  ## a ``LangDef`` object.

  # instead of performing anaylsis of the body directly in the macro and
  # turning the data into a construction expression (via ``newLit``), the
  # code block is turned into a NimNode-literal (via quote) which is then
  # passed to `sem`. This has the major upside of not requiring using
  # `newLit` and getting rid the subsequent analysis/evaluation of the
  # construction.
  # The accent-quotes in the body need to be filtered out, otherwise `quote`
  # would use them for interpolation
  newCall(bindSym"sem", newCall(bindSym"quote", removeQuoted(body)))

proc parse(n: NimNode): TNode =
  template wrap(nk: NodeKind, start: int, body: untyped): untyped =
    var r = TNode(kind: nk)
    for i in start..<n.len:
      let it {.inject.} = n[i]
      r.add body
    r

  case n.kind
  of nnkIntLit:
    TNode(kind: nkNumber, num: rational(n.intVal.int))
  of nnkFloatLit:
    TNode(kind: nkNumber, num: rational(n.floatVal))
  of nnkStrLit:
    TNode(kind: nkString, sym: n.strVal)
  of nnkIdent, nnkSym:
    TNode(kind: nkSymbol, sym: n.strVal)
  of nnkAccQuoted:
    TNode(kind: nkSymbol, sym: n[0].strVal)
  of nnkCurly:
    wrap(nkSet, 0, parse(it))
  of nnkCall:
    wrap(nkConstr, 0, parse(it))
  of nnkTupleConstr:
    wrap(nkTuple, 0, parse(it))
  of nnkObjConstr:
    wrap(nkRecord, 1,
      TNode(kind: nkAssoc, children: @[parse(it[0]), parse(it[1])]))
  of nnkTableConstr:
    wrap(nkMap, 0,
      TNode(kind: nkAssoc, children: @[parse(it[0]), parse(it[1])]))
  of nnkStmtList, nnkStmtListExpr:
    n.expectLen 1
    parse(n[0])
  else:
    error("invalid expression", n)
    TNode()

macro term*(x: untyped): TNode =
  ## Returns the AST for the meta-language term `x`.
  # the NimSkull grammar requires the ``quote`` argument being a statement
  # list...
  let x =
    case x.kind
    of nnkStmtList: x
    else:           newTree(nnkStmtList, x)
  # TODO: take the language as a parameter and use ``semExpr`` instead of
  #       ``parse``
  newCall(bindSym"parse", newCall(bindSym"quote", removeQuoted(x)))
