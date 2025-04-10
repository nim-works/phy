## Implements an interpreter for the full meta-language. The expressions are
## evaluated directly, without an intermediate IR or a VM.

import std/[tables, sugar]
import builtin, bignums, rationals, cps
import types except Node

type
  Failure* = object of CatchableError
    ## Error raised by the interpreter when something cannot be evaluated.

  Node = types.Node[TypeId]
  Bindings = Table[int, Node]

  Frame = object
    scopes: seq[Bindings]
      ## all bindings recorded within the frame. Separated into scopes to make
      ## adding tentative bindings (which may be discarded again) easier

  Trace* = object
    ## Stores an established relation together with the sub-relations
    ## established to prove that it holds.
    id*: int         ## ID of the relation
    rule*: int       ## ID of the used rule
    input*: Node     ## values in input positions
    output*: Node    ## values in output positions
    sub*: seq[Trace]

  Context = object
    relCache: seq[seq[Node]]
      ## the body of a relation is transformed into a proper function prior to
      ## execution, and this sequences caches the transformed bodies. An empty
      ## sequence represents a not-yet-cached entry
    frames: seq[Frame]
      ## stack of frames
    traces: seq[Trace]
      ## list of traces collected during evaluation

  Match = object
    ## The result of matching a term against a pattern.
    case has: bool
    of true:
      ctx: seq[int]
        ## the path to the source term fragment that the hole (if any) matched
      bindings: Bindings
    of false:
      discard

  Next = proc(c: var Context, lang: LangDef, val: sink Node): Node {.contcc.}
    ## type of a continuation

using
  c: var Context
  lang: LangDef

const
  ParamId = -1 ## ID for a function's/relation's parameter binding
  HoleId  = -2 ## ID for hole bindings

proc unreachable() {.noreturn, noinline.} =
  raise AssertionDefect.newException("unreachable")

proc drop[T](x: sink T) {.inline.} =
  ## Utility procedure that does nothing except destroying `x`.
  discard

proc take(x: sink Node, i: int): Node =
  ## Consumes a whole node and returns a single element out of it, dropping
  ## the rest.
  move x[i]

proc extract(term: Node, path: seq[int]): Node =
  ## Returns the term at the given `path`.
  var x {.cursor.} = term
  for it in path.items:
    x = x[it]
  result = x # XXX: unfortunately requires a copy

proc push(c) =
  ## Pushes a new empty scope.
  c.frames[^1].scopes.add default(Bindings)

proc rollback(c) =
  ## Pops the current scope without merging it.
  discard c.frames[^1].scopes.pop()

proc pop(c): Bindings =
  c.frames[^1].scopes.pop()

proc merge(a: var Bindings, b: Bindings) =
  ## Merges the bindings from `b` into `a`. Groups are automatically
  ## concatenated.
  for key, val in b.pairs:
    a.withValue key, valP:
      assert valP.kind == nkGroup
      assert val.kind == nkGroup
      valP.children.add val.children
    do:
      a[key] = val

proc merge(c; b: Bindings) =
  ## Merges the given bindings into the current scope.
  c.frames[^1].scopes[^1].merge(b)

proc merge(c) =
  merge(c, pop(c))

proc addBinding(c; id: int, n: sink Node) =
  c.frames[^1].scopes[^1][id] = n

proc wrap(a: sink Bindings): Bindings =
  for val in a.mvalues:
    val = tree(nkGroup, val)
  result = a

proc wrap(a: sink Match): Match =
  result = a
  result.bindings = wrap(result.bindings)

proc merge(a: var Match, b: Match) =
  a.bindings.merge(b.bindings)
  a.ctx.add b.ctx

proc matches(lang; pat: Node, term: Node): Match

proc matchList(lang; pat: Node, term: Node): Match =
  ## Matches the sequence-like `term` against the sequence-like pattern `pat`.
  # the implementation uses a non-deterministic finite-state machine realized
  # using continuation-passing-style. The match procedure takes a pattern, a
  # cursor (term + index), the previous match state (for tracking the
  # bindings), and a continuation as input
  type Cont = proc(lang: LangDef, term: Node, i: int, b: sink Match): Match
  template cont(body: untyped): untyped {.dirty.} =
    # cannot use the `=>` macro because of the sink parameter
    proc tmp(lang; term: Node, i: int, sub: sink Match): Match {.gensym.} =
      body
    tmp

  proc match(lang; pat, term: Node, i: int, b: sink Match, then: Cont): Match =
    proc rep(lang; pat, term: Node, i: int, b: sink Match, then: Cont): Match =
      let m = match(lang, pat[0], term, i, Match(has: true),
        cont(rep(lang, pat, term, i, wrap(sub), then)))
      if m.has:
        b.merge(m) # merge the bindings
        b
      else:
        then(lang, term, i, b)

    case pat.kind
    of nkOneOrMore:
      let m = match(lang, pat[0], term, i, Match(has: true),
        cont(rep(lang, pat, term, i, wrap(sub), then)))
      if m.has:
        b.merge(m)
        b
      else:
        Match(has: false)
    of nkZeroOrMore:
      rep(lang, pat, term, i, b, then)
    of nkGroup:
      # all patterns in the group must match sequentially
      proc step(lang; term: Node, i, j: int, b: sink Match): Match =
        if j < pat.len:
          match(lang, pat[j], term, i, b,
            cont(step(lang, term, i, j + 1, sub)))
        else:
          then(lang, term, i, b)

      step(lang, term, i, 0, b)
    elif i < term.len:
      case pat.kind
      of nkContext, nkHole:
        assert b.ctx.len == 0, "multiple holes?"
        b.ctx = @[i]
        b.bindings[HoleId] = pat # remember the shape of the hole for later
        then(lang, term, i + 1, b)
      else:
        var tmp = matches(lang, pat, term[i])
        if tmp.has:
          if tmp.ctx.len > 0: # was there a "hole match"?
            tmp.ctx.insert(i) # prepend the position to the list
          b.merge(tmp)
          then(lang, term, i + 1, b)
        else:
          Match(has: false)
    else:
      Match(has: false)

  proc step(lang; pat, term: Node, i, j: int, b: sink Match): Match =
    if j < pat.len:
      match(lang, pat[j], term, i, b,
        cont(step(lang, pat, term, i, j + 1, sub)))
    else:
      # the list pattern only matches the term if the term is fully consumed
      if term.len == i: b
      else:             Match(has: false)

  step(lang, pat, term, 0, 0, Match(has: true))

proc matches(lang; pat, term: Node): Match =
  ## The heart of the pattern matcher (for non-recursive patterns).
  template test(cond: bool): Match =
    Match(has: cond)
  case pat.kind
  of nkTrue, nkFalse:
    test term.kind == pat.kind
  of nkNumber:
    test term.kind == nkNumber and term.num == pat.num
  of nkSymbol, nkString:
    test term.kind == pat.kind and term.sym == pat.sym
  of nkConstr:
    if term.kind == nkConstr:
      matchList(lang, pat, term)
    else:
      Match(has: false)
  of nkTuple:
    if term.kind == nkTuple and term.len == pat.len:
      var res = Match(has: true)
      for i, it in term.children.pairs:
        let tmp = matches(lang, pat[i], it)
        if tmp.has:
          res.merge(tmp)
        else:
          return tmp
      res
    else:
      Match(has: false)
  of nkHole, nkContext:
    # the hole is recorded as a special binding in order to be looked up again
    # later for the purpose of post-matching
    Match(has: true, bindings: toTable({HoleId: pat}))
  of nkPlug:
    # remember the plug pattern and matched term, for later resolution
    let plug = tree(nkGroup, tree(nkTuple, pat, term))
    Match(has: true, bindings: toTable({HoleId: plug}))
  of nkBind:
    if pat.len == 1 or matches(lang, pat[1], term).has:
      Match(has: true, bindings: toTable({pat[0].id: term}))
    else:
      Match(has: false)
  of nkType:
    case lang[pat.typ].kind
    of tkVoid, tkAll:
      # TODO: address the type-system issue(s) that results in 'void'
      #       and 'all' being the same thing at this stage (they shouldn't be)
      Match(has: true)
    of tkBool:
      test term.kind in {nkTrue, nkFalse}
    of tkInt:
      test term.kind == nkNumber and term.num.isInt
    of tkRat:
      test term.kind == nkNumber
    of tkList:
      # TODO: not really correct...
      test term.kind == nkString
    of tkRecord:
      # TODO: should not reach here. Static type checking should elide these
      #       patterns
      Match(has: true)
    of tkFunc:
      # TODO: same as above
      test term.kind in {nkMap, nkSet}
    of tkData:
      for it in lang[pat.typ].constr.items:
        if matches(lang, it, term).has:
          return Match(has: true)
      Match(has: false)
    of tkSum:
      for it in lang[pat.typ].children.items:
        if matches(lang, Node(kind: nkType, typ: it), term).has:
          return Match(has: true)
      Match(has: false)
    else:
      unreachable()
  of nkZeroOrMore:
    test term.kind == nkGroup or term.kind == nkString
  of nkOneOrMore:
    test (term.kind == nkGroup and term.len > 0) or
         (term.kind == nkString and term.sym.len > 0)
  of nkGroup:
    # matching a standalone list
    if term.kind == nkGroup:
      matchList(lang, pat, term)
    else:
      Match(has: false)
  else:
    unreachable()

template catch(c: var Context, body, els: untyped) =
  ## Runs `body`, with `els` being executed if the former raises a ``Failure``.
  let frames = c.frames.len
  let scopes = c.frames[frames - 1].scopes.len
  try:
    body
  except Failure:
    # restore the previous context first:
    c.frames.setLen(frames)
    c.frames[frames - 1].scopes.shrink(scopes)
    els

proc interpret*(c; lang; n: Node, then: sink Next): Node {.tailcall.}

proc eval(c; lang; n: Node): Node =
  ## Evaluates `n`, returning the result or raising an exception. Important:
  ## this breaks the continuation chain.
  interpret(c, lang, n,
    proc(c; lang; val: sink Node): Node {.cont.} = val)

proc interpretFunc(c; lang; id: int, args: sink Node): Node =
  ## Evaluates an invocation of function `id` with argument `args`.
  if lang.functions[id].body.kind == nkHole: # no body?
    # the in/notin functions with function operands are special
    if lang.functions[id].name in ["in", "notin"] and args[1].kind == nkFunc:
      var res: bool
      c.catch:
        discard interpretFunc(c, lang, args[1].id, args[0])
        res = true # argument is in the function's domain
      do:
        res = false # argument is not in the function's domain

      if lang.functions[id].name == "notin":
        res = not res

      if res: result = Node(kind: nkTrue)
      else:   result = Node(kind: nkFalse)
    else:
      # must be a built-in function
      result = (functions[lang.functions[id].name])(args)
  else:
    c.frames.add(Frame(scopes: @[toTable({ParamId: args})]))
    result = eval(c, lang, lang.functions[id].body)
    c.frames.shrink(c.frames.len - 1) # pop the frame again

proc makeTuple(args: sink seq[Node]): Node =
  if args.len == 1:
    args[0] # don't create single-element tuples
  else:
    Node(kind: nkTuple, children: args)

proc transformRelation(lang; n: Node): Node =
  ## Transforms usage of a relation to a 'matches' expression, if the relation
  ## has designated output parameters.
  assert n.kind == nkCall
  var outputs: seq[Node]
  var source = Node(kind: nkCall, children: @[n[0]])
  for i, it in lang.relations[n[0].id].params.pairs:
    if it.input:
      source.add n[i + 1]
    else:
      outputs.add n[i + 1]
  if outputs.len == 0:
    result = source # the call can stay as is
  else:
    result = tree(nkMatches, makeTuple(outputs), source)

proc transformRule(lang; n, els: Node): (Node, Node) =
  ## For rules of relations with designated outputs, transforms the rule
  ## into a (possibly non-total) function mapping the inputs to a value.
  ## For rules of relations with no designated outputs, transforms the rule
  ## into a function mapping the inputs to a boolean value.
  ## In both cases, returns the bubbled-up inputs and the function body.
  if n.kind == nkImplies:
    let (inp, next) = transformRule(lang, n[1], els)

    proc transform(lang; n: Node): Node =
      if n.kind == nkCall and n[0].kind == nkRelation:
        transformRelation(lang, n)
      else:
        n

    var r: Node
    if n[0].kind == nkUnpack:
      # keep the wrapping unpack expression
      r = n[0]
      r.children[^1] = transform(lang, n[0][^1])
    else:
       r = transform(lang, n[0])

    (inp, tree(nkIf, r, next, Node(kind: nkFail)))
  else:
    # both the overall input and output is taken from the final implied
    # relation. We re-use ``transformRelation`` for spliting the relation
    let x = transformRelation(lang, n)
    if x.kind == nkMatches:
      (makeTuple(x[1].children[1..^1]), x[0])
    else:
      (makeTuple(x.children[1..^1]), Node(kind: nkTrue))

proc transformBody(lang; rel: Relation[TypeId]): seq[Node] =
  result.newSeq(rel.rules.len)
  for i, it in result.mpairs:
    let t = transformRule(lang, rel.rules[i].body, Node(kind: nkFail))
    it = tree(nkIf,
      tree(nkMatches, t[0], Node(kind: nkVar, id: ParamId)),
      t[1],
      Node(kind: nkFail))

proc interpretRelation(c; lang; id: int, args: sink Node): Node =
  ## Evaluates an invocation of the evaluator function for relation `id`.
  if id >= c.relCache.len or c.relCache[id].len == 0:
    # TODO: perform the transformation outside of interpretation, so that it
    #       doesn't take place anew for each interpreter invocation
    c.relCache.setLen(max(c.relCache.len, id + 1))
    c.relCache[id] = transformBody(lang, lang.relations[id])

  c.frames.add(Frame(scopes: @[{ParamId: args}.toTable]))
  let original = move c.traces
  var rule = -1

  # the cache's storage may change during the loop, so don't use an `items`
  # iterator
  for i in 0..<c.relCache[id].len:
    c.catch:
      c.push()
      result = eval(c, lang, c.relCache[id][i])
      c.rollback() # discard all bindings; they're no longer needed
      rule = i
      break
    do:
      discard "try the next rule"

  c.frames.shrink(c.frames.len - 1) # pop the frame
  if result.kind == nkFail:
    # is it a boolean relation?
    for it in lang.relations[id].params.items:
      if not it.input:
        # it isn't, fail
        raise Failure.newException("")
    # it is, return false
    result = Node(kind: nkFalse)
  else:
    # success!
    let trace = Trace(id: id, rule: rule, input: args, output: result,
                      sub: move c.traces)
    # restore the previous list and remember the successful relation
    c.traces = original
    c.traces.add trace

proc matchRPattern(c; lang; id: int, n: Node, ctx: seq[int],
                   then: proc(c: var Context, lang: LangDef, n: Node, ctx: seq[int]): Node): Node =
  ## Implements R-pattern matching. Tries to decompose `n` into a term-with-
  ## hole and a term. On finding a candidate, `then` is invoked. If a `then`
  ## invocation succeeds, returns with the result of the invocation, otherwise
  ## continues looking for a decomposition.
  for pat in lang.matchers[id].patterns.items:
    let m = matches(lang, pat, n)
    if m.has:
      c.catch:
        let (p, t) = (m.bindings[HoleId], extract(n, m.ctx))
        if p.kind == nkContext:
          # recurse into the R-pattern
          result = matchRPattern(c, lang, p.id, t, ctx & m.ctx, then)
        else:
          # try to plug the hole
          c.push()
          result = then(c, lang, t, ctx & m.ctx) # may raise
          c.merge()
        # found a matching pattern
        break
      do:
        discard "try the next pattern"
    # else: try the next pattern

  if result.kind == nkFail:
    # no pattern matched
    raise Failure.newException("")

proc withHole(n: Node, path: openArray[int]): Node =
  ## Returns `n` with the node at `path` replaced with a hole.
  if path.len == 0:
    return Node(kind: nkHole)

  case n.kind
  of withChildren:
    result = Node(kind: n.kind)
    result.children.newSeq(n.len)
    for i, it in n.children.pairs:
      if i == path[0]:
        result.children[i] = withHole(it, path.toOpenArray(1, path.high))
      else:
        result.children[i] = it
  else:
    unreachable()

proc plug(term, hole: Node): Node =
  ## Given a term-with-a-hole `term`, plugs the hole with `hole` and returns
  ## the result.
  case term.kind
  of withChildren:
    result = Node(kind: term.kind)
    result.children.newSeq(term.len)
    for i, it in term.children.pairs:
      result.children[i] = plug(it, hole)
  of nkHole:
    result = hole
  of nkFail, nkFalse, nkTrue, nkNumber, nkString, nkSymbol, nkFunc, nkRelation,
     nkContext, nkVar, nkType:
    result = term

proc prepareCond(n: sink Node): Node =
  if n.kind == nkGroup:
    for it in n.children.items:
      if it.kind == nkFalse:
        return Node(kind: nkFalse)
    result = Node(kind: nkTrue)
  else:
    result = n

proc interpretAll(c; lang; s: openArray[Node]): seq[Node] =
  ## Interprets all expression in `s`, also delimiting all continuations
  ## created within.
  result.newSeq(s.len)
  for i, it in result.mpairs:
    it = eval(c, lang, s[i])

proc interpretMatch(c; lang; pat, term: Node, then: sink Next): Node =
  ## Tries matching `term` with `pat`, and on success, adds the captures to
  ## the context and invokes `then` with `nkTrue`; `nkFalse` otherwise.
  var m = matches(lang, pat, term);
  if m.has:
    var plugs: Node
    # did plug patterns participate in the match?
    if m.bindings.pop(HoleId, plugs):
      # yes, resolve them
      c.merge(m.bindings)
      proc inner(c; lang; j: int): Node {.closure.} =
        # TODO: make `inner` a tailcall procedure
        if j < plugs.len:
          let (pat, term) = (plugs[j][0], plugs[j][1])
          assert pat.kind == nkPlug
          let rpat =
            if pat[0].kind == nkBind: pat[0][1].id
            else:                     pat[0].id
          matchRPattern(c, lang, rpat, term, @[],
            (c: var Context, lang, res, ctx) => (
              # try the plugged-with pattern:
              interpretMatch(c, lang, pat[1], res,
                proc(c; lang; val: sink Node): Node {.
                    cont: (ptr pat, ptr term, ptr ctx, j, inner).} =
                  if val.kind == nkTrue:
                    if pat[0].kind == nkBind:
                      # bind the context to the given name
                      c.addBinding(pat[0][0].id, withHole(term, ctx))
                    inner(c, lang, j + 1) # continue with the next plug
                  else:
                    raise Failure.newException(""))))
        else:
          # all plugs could be resolved successfully
          then(c, lang, Node(kind: nkTrue))
      inner(c, lang, 0)
    else:
      # no plug patterns; the match was successful
      c.merge(m.bindings)
      then(c, lang, Node(kind: nkTrue))
  else:
    # no match
    then(c, lang, Node(kind: nkFalse))

proc interpret(c; lang; n: Node, then: sink Next): Node {.tailcall.} =
  ## Evaluates expression `n`. Evaluation uses continuation-passing-style
  ## (=CPS): instead of returning the value, the `then` procedure is
  ## invoked with it; this makes the non-deterministic plug pattern matching
  ## possible.
  # for reasons of code complexity, evaluation of some intermediate results
  # does not use CPS, meaning that any plug pattern matching within doesn't
  # work
  case n.kind
  of nkFail:
    raise Failure.newException("")
  of nkSymbol:
    then(c, lang, n)
  of nkFalse, nkTrue, nkNumber, nkFunc, nkString, nkRelation:
    then(c, lang, n)
  of nkTuple:
    then(c, lang,
      Node(kind: nkTuple, children: interpretAll(c, lang, n.children)))
  of nkGroup:
    then(c, lang,
      Node(kind: nkGroup, children: interpretAll(c, lang, n.children)))
  of nkSet:
    then(c, lang,
      Node(kind: nkSet, children: interpretAll(c, lang, n.children)))
  of nkConstr:
    proc append(to: var seq[Node], n: sink Node) {.nimcall.} =
      # groups in this context can have a nesting depth of at most 2, so using
      # recursion here is fine
      case n.kind
      of nkGroup:
        for i in 0..<n.len:
          append(to, move n[i])
      else:
        to.add n

    var elems: seq[Node]
    for it in n.children.items:
      append(elems, eval(c, lang, it))

    then(c, lang, Node(kind: nkConstr, children: elems))
  of nkVar:
    # look through the scopes:
    for i in countdown(c.frames[^1].scopes.high, 0):
      if n.id in c.frames[^1].scopes[i]:
        return then(c, lang, c.frames[^1].scopes[i][n.id])
    # assuming that the interpreter and type-checker work, a missing binding
    # for a name is fine: it means that a repetition matched zero items
    then(c, lang, Node(kind: nkGroup))
  of nkImplies:
    interpret(c, lang, n[0],
      proc(c; lang; val: sink Node): Node {.cont: (ptr n, then).} =
        if val.kind != nkTrue:
          then(c, lang, val)
        else:
          drop val
          interpret(c, lang, n[1], then))
  of nkMatches:
    interpret(c, lang, n[1],
      proc(c; lang; val: sink Node): Node {.cont: (ptr n, then).} =
        interpretMatch(c, lang, n[0], val, then))
  of nkMap:
    var elems = newSeq[Node](n.len)
    for i, it in n.children.pairs:
      elems[i] = tree(nkAssoc,
        eval(c, lang, it[0]),
        eval(c, lang, it[1]))
    then(c, lang, Node(kind: nkMap, typ: n.typ, children: elems))
  of nkRecord:
    var elems = newSeq[Node](n.len)
    for i, it in n.children.pairs:
      elems[i] = tree(nkAssoc, it[0], eval(c, lang, it[1]))
    then(c, lang, Node(kind: nkRecord, typ: n.typ, children: elems))
  of nkIf:
    interpret(c, lang, n[0],
      proc(c; lang; val: sink Node): Node {.cont: (ptr n, then).} =
        let val = prepareCond(val); # fold boolean lists first
        if val.kind == nkTrue:
          drop val
          interpret(c, lang, n[1], then)
        else:
          assert val.kind == nkFalse
          drop val
          interpret(c, lang, n[2], then))
  of nkMatch:
    proc step(c; lang; n: Node, val: sink Node, i: int,
              then: sink Next): Node {.tailcall.} =
      if i < n.len:
        # a multi-pattern 'of' branch is turned into a single-tuple pattern
        # match
        let m = block: matches(lang, makeTuple(n[i].children[0..^2]), val)
        if m.has:
          # found a branch that applies
          c.merge(m.bindings)
          drop val
          drop m
          interpret(c, lang, n[i][n[i].len - 1], then)
        else:
          # try the next branch
          drop m
          step(c, lang, n, val, i + 1, then)
      else:
        # no branch applies, fail
        raise Failure.newException("")

    if n[0].kind == nkHole:
      # ``case _`` means "use the current parameter"
      let tmp = c.frames[^1].scopes[0][ParamId]
      step(c, lang, n, tmp, 1, then)
    else:
      interpret(c, lang, n[0],
        proc(c; lang; val: sink Node): Node {.cont: (ptr n, then).} =
          step(c, lang, n, val, 1, then))
  of nkCall:
    interpret(c, lang, n[0],
      proc(c; lang; val: sink Node): Node {.cont: (ptr n, then).} =
        let args = interpretAll(c, lang, n.children.toOpenArray(1, n.len - 1))
        case val.kind
        of nkFunc:
          let id = val.id
          drop val
          then(c, lang, interpretFunc(c, lang, id, makeTuple(args)))
        of nkRelation:
          let id = val.id
          drop val
          then(c, lang, interpretRelation(c, lang, id, makeTuple(args)))
        of nkGroup:
          # it's a list lookup
          let idx = args[0].num.toInt
          drop args
          let L = bignum(val.len)
          if idx >= 0'n and idx < L:
            let i = idx.toInt.int
            drop L
            drop idx
            then(c, lang, take(val, i))
          else:
            raise Failure.newException("")
        of nkMap:
          # it's a map lookup
          for it in val.children.items:
            if it[0] == args[0]:
              let ret = it[1]
              drop args
              drop val
              return then(c, lang, ret)
          raise Failure.newException("")
        of nkSet:
          # it's a set lookup
          for it in val.children.items:
            if it == args[0]:
              drop args
              drop val
              return then(c, lang, Node(kind: nkTrue))
          drop args
          drop val
          then(c, lang, Node(kind: nkFalse))
        else:
          unreachable())
  of nkProject:
    interpret(c, lang, n[0],
      proc(c; lang; val: sink Node): Node {.cont: (ptr n, then).} =
        # pick the correct value using the name:
        for it in val.children.items:
          if it[0].sym == n[1].sym:
            let ret = it[1]
            drop val
            return then(c, lang, ret)
        unreachable())
  of nkPlug:
    interpret(c, lang, n[0],
      proc(c; lang; val: sink Node): Node {.cont: (ptr n, then).} =
        interpret(c, lang, n[1],
          proc(c; lang; pl: sink Node): Node {.cont: (val, then).} =
            let p = plug(val, pl)
            drop val
            drop pl
            then(c, lang, p)))
  of nkUnpack:
    var inputs: seq[Node]
    for i in 0..<n.len - 1:
      inputs.add eval(c, lang, n[i][1])

    var output: seq[Node]
    for i in 0..<inputs[0].len:
      c.push()
      # bind elements from the input sequences to the specified names...
      for x, it in inputs.pairs:
        c.addBinding(n[x][0].id, it[output.len])
      c.push()
      # ...then execute the body:
      output.add eval(c, lang, n[^1])
      let tmp = c.pop()
      c.rollback() # drop the input bindings
      c.merge(wrap(tmp)) # group-merge the collected bindings

    drop inputs
    then(c, lang, Node(kind: nkGroup, children: output))
  else:
    echo n.kind
    unreachable()

proc interpret*(lang; n: Node): (Node, Trace) =
  ## Evaluates expression `n` and returns the resulting value plus a trace
  ## of all relations established in order to reach this result.
  var c = Context()
  result[0] = eval(c, lang, n)
  if c.traces.len > 0:
    result[1] = c.traces[0]
