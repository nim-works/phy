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

  LogEntryKind* = enum
    lekRelation ## start of a relation
    lekRule     ## start of a rule
    lekMatch    ## a rule applied
    lekMismatch ## a rule didn't apply
    lekFailure  ## a relation failed
    lekSuccess  ## a rule and thus relation succeeded

  LogEntry* = object
    ## An entry in the execution log.
    case kind*: LogEntryKind
    of lekRelation, lekMatch:
      id*: int
      data*: Node ## inputs or outputs
    of lekRule:
      rule*: int
    of lekFailure, lekSuccess, lekMismatch:
      discard

  Context = object
    relCache: seq[seq[Node]]
      ## the body of a relation is transformed into a proper function prior to
      ## execution, and this sequences caches the transformed bodies. An empty
      ## sequence represents a not-yet-cached entry
    frames: seq[Frame]
      ## stack of frames

    doLog: bool
      ## whether logging is enabled
    logs: seq[LogEntry]
      ## if logging is enabled, accumulates log entries describing
      ## the execution

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

proc merge(a: var Match, b: sink Match) =
  a.bindings.merge(b.bindings)
  a.ctx.add b.ctx

proc matches(lang; pat: Node, term: Node): Match

proc matchList(lang; pat, term: Node): Match {.tailcall.} =
  ## Matches the sequence-like `term` against the sequence-like pattern `pat`.
  type
    PLNext = proc(a: LangDef, b: int, c: sink Match): Match {.contcc.}
    Rest = proc(a: LangDef, b: int, c: sink Match,
                d: sink PLNext): Match {.contcc.}
      ## the continuation representing the rest of the pattern sequence

  proc step(lang; pat, term: Node, pi, ti: int, b: sink Match,
            ret: sink PLNext): Match {.tailcall.}

  proc rep(lang; pat, term: Node, ti: int, b: sink Match, rest: sink Rest,
           ret: sink PLNext): Match {.tailcall.} =
    # note: `a* rest` is the same as `(a a* rest) | rest`
    # try the repetition's content:
    step(lang, pat, term, 0, ti, Match(has: true),
      proc(lang; ti2: int, m: sink Match): Match {.
          cont: (ptr pat, ptr term, rest, b, ti, ret).} =
        if m.has:
          # it's a match! greedily try to continue with the repetition
          rep(lang, pat, term, ti2, wrap(m), rest,
            proc(lang; ti2: int, m: sink Match): Match {.
                cont: (ti, b, rest, ret).} =
              if m.has:
                # success! the repetition + rest was successful
                b.merge(m)
                drop rest
                ret(lang, ti2, b)
              else:
                # continuing would result in a failure; backtrack
                drop m
                rest(lang, ti, b, ret))
        else:
          # no match, try `rest`
          drop m
          rest(lang, ti, b, ret))

  proc step(lang; pat, term: Node, pi, ti: int, b: sink Match,
            ret: sink PLNext): Match {.tailcall.} =
    ## Represents the body of a for-loop iterating over `pat`, with `pi` being
    ## the loop variable (an index into `pat`). `ti` is a cursor into `term`.
    if pi == pat.len:
      # end of pattern
      return ret(lang, ti, b)

    case pat[pi].kind
    of nkOneOrMore:
      step(lang, pat[pi], term, 0, ti, Match(has: true),
        proc(lang; ti: int, m: sink Match): Match {.
            cont: (ptr pat, ptr term, b, pi, ret).} =
          if not m.has:
            drop b
            return ret(lang, 0, m)

          b.merge(wrap(m))
          rep(lang, pat[pi], term, ti, b,
            proc(lang; ti: int, m: sink Match, ret: sink PLNext): Match {.
                cont: (ptr pat, ptr term, pi).} =
              step(lang, pat, term, pi + 1, ti, m, ret)
            , ret))
    of nkZeroOrMore:
      rep(lang, pat[pi], term, ti, b,
        proc(lang; ti: int, m: sink Match, ret: sink PLNext): Match {.
            cont: (ptr pat, ptr term, pi).} =
          step(lang, pat, term, pi + 1, ti, m, ret),
        ret)
    of nkGroup:
      # all patterns in the group must match sequentially. Start a nested for-
      # loop for the group
      step(lang, pat[pi], term, 0, ti, b,
        proc(lang; ti: int, m: sink Match): Match {.
            cont: (ptr pat, ptr term, ret, pi).} =
          if m.has:
            step(lang, pat, term, pi + 1, ti, m, ret)
          else:
            ret(lang, 0, m))
    elif ti < term.len:
      case pat[pi].kind
      of nkContext, nkHole:
        assert b.ctx.len == 0, "multiple holes?"
        b.ctx = @[ti]
        b.bindings[HoleId] = pat[pi] # remember the shape of the hole for later
        step(lang, pat, term, pi + 1, ti + 1, b, ret)
      else:
        var tmp = matches(lang, pat[pi], term[ti])
        if tmp.has:
          if tmp.ctx.len > 0: # was there a "hole match"?
            tmp.ctx.insert(ti) # prepend the position to the list
          b.merge(tmp)
          step(lang, pat, term, pi + 1, ti + 1, b, ret)
        else:
          drop b
          ret(lang, 0, tmp)
    else:
      drop b
      ret(lang, 0, Match(has: false))

  step(lang, pat, term, 0, 0, Match(has: true),
    proc(lang; i: int, m: sink Match): Match {.cont: (ptr term).} =
      # the list pattern only matches the term if the term is fully consumed
      if m.has and term.len == i:
        m
      else:
        Match(has: false))

proc matches(lang; typ: TypeId, term: Node): Match =
  template test(cond: bool): Match =
    Match(has: cond)

  case lang[typ].kind
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
  of tkSum:
    for it in lang[typ].children.items:
      if matches(lang, it, term).has:
        return Match(has: true)
    Match(has: false)
  of tkPat:
    matches(lang, lang[typ].pat, term)
  else:
    unreachable()

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
    matches(lang, pat.typ, term)
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

template log(c: var Context, entry: LogEntry) =
  ## If logging is enabled, evaluates `entry` and adds it to the log.
  if c.doLog:
    c.logs.add entry

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
  var rule = -1

  c.log LogEntry(kind: lekRelation, id: id, data: args)

  # the cache's storage may change during the loop, so don't use an `items`
  # iterator
  for i in 0..<c.relCache[id].len:
    c.log LogEntry(kind: lekRule, rule: i)
    c.catch:
      c.push()
      result = eval(c, lang, c.relCache[id][i])
      c.rollback() # discard all bindings; they're no longer needed
      rule = i
      break
    do:
      c.log LogEntry(kind: lekMismatch)
      # try the next rule

  c.frames.shrink(c.frames.len - 1) # pop the frame
  if result.kind == nkFail:
    # is it a boolean relation?
    for it in lang.relations[id].params.items:
      if not it.input:
        # it isn't, fail
        c.log LogEntry(kind: lekFailure)
        raise Failure.newException("")
    # it is, return false
    result = Node(kind: nkFalse)
  else:
    c.log LogEntry(kind: lekMatch, id: id, data: result)

  c.log LogEntry(kind: lekSuccess)

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

proc interpret*(lang; n: Node): Node =
  ## Evaluates expression `n` and returns the resulting value, or an `nkFail`
  ## node, if evaluation failed.
  var c = Context()
  result =
    try:            eval(c, lang, n)
    except Failure: Node(kind: nkFail)

proc interpretAndLog*(lang; n: Node): (Node, seq[LogEntry]) =
  ## Similar to `interpret <#interpret,LangDef,Node>`_, but with execution
  ## logging enabled.
  var c = Context(doLog: true)
  result[0] =
    try:            eval(c, lang, n)
    except Failure: Node(kind: nkFail)
  result[1] = c.logs
