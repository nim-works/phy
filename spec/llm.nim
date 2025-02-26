## Implements the data types and evaluator for a simple purely functional
## StandardML-esque language called LLM (low-level meta-language).
##
## It's meant as an intermediate language to lower the higher-level meta-
## language to.

import
  std/[strutils, tables]

type
  ExprKind* = enum
    # leafs
    ekFail
    ekFalse, ekTrue
    ekNumber
    ekString
    ekFunc
    ekVar
    ekNil
    ekWildcard
    # non-leafs
    ekUp     ## up(up | var) - de-Bruijn indexing
    ekCons   ## cons(e, cons|nil) - list constructor
    ekTuple
    ekLambda ## lambda(num, var, e)
    ekLetrec ## letrec(var, lambda, e) - self-recursive lambda
    # note: self-recursive functions can be implemented using just lambda
    # expressions, but letrec makes them easier to write, read, and spot
    ekApp    ## app(e, e)
    ekIf     ## if(e, e, e)
    ekTry    ## try(e, var, e, e)
    ekMatch  ## match(e, branch+)
    ekBranch ## branch(pat, e)

  Expr* = object
    case kind*: ExprKind
    of ekFail, ekFalse, ekTrue, ekNil, ekWildcard:
      discard
    of ekVar, ekFunc:
      id*: int
    of ekString, ekNumber:
      val*: string
    of ekUp, ekCons, ekTuple, ekApp, ekIf, ekTry, ekMatch, ekBranch, ekLambda,
       ekLetrec:
      children*: seq[Expr]

  LLFunction* = object
    ## Represents a named function. All functions have exactly one parameter.
    case isNative*: bool
    of true:
      native*: proc(val: Expr): Expr {.nimcall.}
    of false:
      body*: Expr

  Value = Expr ## the subset of expressions representing values
  Frame = object
    # frames form a cactus stack
    parent: int
    vars: Table[int, Value]

  Context = object
    frames: seq[Frame]

  Failure* = object of CatchableError
    ## Used for implementing fail/try.

const
  LeafNodes* = {ekFail..ekWildcard}

using
  c: var Context
  funcs: seq[LLFunction]

template atom*(k: ExprKind): Expr =
  Expr(kind: k)

template expr*(k: ExprKind, args: varargs[Expr]): Expr =
  Expr(kind: k, children: @args)

template vid*(x: int): Expr =
  Expr(kind: ekVar, id: x)

template num*(x: string): Expr =
  Expr(kind: ekNumber, val: x)

template `[]`(e: Expr, i: int): untyped =
  e.children[i]

template `[]`*(e: Expr, i: BackwardsIndex): untyped =
  e.children[i]

func len*(e: Expr): int {.inline.} = e.children.len

iterator items*(e: Expr): lent Expr =
  for it in e.children.items:
    yield it

proc render*(e: Expr, indent = 0): string =
  ## Renders and formats `e` and returns the result.
  template newline(): string =
    "\n" & repeat("  ", indent)

  proc sub(e: Expr, indent: int): string {.nimcall.} =
    if e.kind in {ekMatch, ekIf, ekLetrec, ekTry}:
      result.add newline()
    result.add render(e, indent)

  case e.kind
  of ekFail:     result = "fail"
  of ekTrue:     result = "true"
  of ekFalse:    result = "false"
  of ekNil:      result = "."
  of ekWildcard: result = "_"
  of ekFunc:     result = "f_" & $e.id
  of ekNumber:   result = e.val
  of ekVar:      result = "v_" & $e.id
  of ekString:   result = escape(e.val)
  of ekUp:       result = "λ" & render(e[0], indent)
  of ekCons:
    result = "["
    var it {.cursor.} = e
    while it.kind == ekCons:
      if result.len > 1:
        result.add ", "
      result.add render(it[0], indent)
      it = it[1]
    if it.kind != ekNil:
      result.add ", "
      result.add render(it, indent)
      result.add " ..."
    result.add "]"
  of ekMatch:
    result = "match "
    result.add render(e[0], indent + 1)
    for i in 1..<e.children.len:
      result.add newline()
      result.add render(e[i], indent)
  of ekTry:
    result = "try "
    result.add sub(e[0], indent + 1)
    result.add newline() & "then "
    result.add render(e[1], indent)
    result.add " "
    result.add sub(e[2], indent + 1)
    result.add newline() & "else "
    result.add sub(e[3], indent + 1)
  of ekIf:
    result = "if " & sub(e[0], indent + 1)
    result.add newline()
    result.add "then " & sub(e[1], indent + 1)
    result.add newline()
    result.add "else " & sub(e[2], indent + 1)
  of ekApp:
    if e[1].kind == ekTuple:
      result = render(e[0], indent)
      result.add render(e[1], indent)
    else:
      result = "("
      result.add render(e[0], indent)
      result.add " "
      result.add render(e[1], indent)
      result.add ")"
  of ekTuple:
    result.add "("
    for i in 0..<e.children.len:
      if i > 0:
        result.add ", "
      result.add render(e[i], indent)
    result.add ")"
  of ekBranch:
    result.add "| "
    result.add render(e[0], indent)
    result.add ": "
    result.add sub(e[1], indent + 1)
  of ekLambda:
    # the number in the first slot is only relevant for the evaluator
    result.add render(e[1], indent)
    result.add " => "
    result.add sub(e[2], indent + 1)
  of ekLetrec:
    result.add "letrec "
    result.add render(e[0], indent)
    result.add " "
    result.add sub(e[1], indent + 1)
    result.add "\n" & repeat("  ", indent + 1)
    result.add render(e[2], indent + 1)

proc match(f: var Frame, pat: Expr, val: Value): bool =
  ## Implements the pattern matching for ``match`` expressions.
  case pat.kind
  of ekWildcard:
    true
  of ekNil:
    val.kind == ekNil
  of ekNumber:
    val.kind == ekNumber and val.val == pat.val
  of ekString:
    val.kind == ekString and val.val == pat.val
  of ekVar:
    # bind the value to the ID. Since ID can bo bound to only once, there's no
    # need to undo the binding if a latter pattern doesn't match
    f.vars[pat.id] = val
    true
  of ekCons:
    val.kind == ekCons and match(f, pat[0], val[0]) and
      match(f, pat[1], val[1])
  of ekTuple:
    if val.kind == ekTuple and pat.len == val.len:
      for i in 0..<val.len:
        if not match(f, pat[i], pat[i]):
          return false
      true
    else:
      false
  of ekApp:
    val.kind == ekApp and match(f, pat[0], pat[0]) and
      match(f, pat[1], pat[1])
  else:
    raise Defect.newException("") # TODO: use unreachable

template with(c: var Context; f: Frame, e: Expr): Expr =
  c.frames.add f
  defer: c.frames.shrink(c.frames.len - 1)
  e

proc eval*(funcs; c; e: Expr): Expr

proc eval(funcs; c; id: int, e: Expr): Expr =
  ## Evaluates an application of the given function to `e`.
  if funcs[id].isNative:
    funcs[id].native(e)
  else:
    c.with Frame(parent: c.frames.high, vars: toTable({0: e})):
      eval(funcs, c, funcs[id].body)

proc eval*(funcs; c; e: Expr): Expr =
  ## The evaluator procedure implementing the full LLM language. Raises a
  ## ``Failure`` if there's an uncaught exception.
  template eval(e): Expr =
    eval(funcs, c, e)
  case e.kind
  of ekTrue, ekFalse, ekString, ekNumber, ekFunc, ekNil:
    e
  of ekFail:
    raise Failure.newException("")
  of ekVar:
    c.frames[^1].vars[e.id]
  of ekUp:
    var f = c.frames.high
    var n {.cursor.} = e
    while n.kind != ekVar:
      f = c.frames[f].parent
      n = n[0]
    c.frames[f].vars[n.id]
  of ekCons:
    expr(ekCons, eval(e[0]), eval(e[1]))
  of ekTuple:
    var elems = newSeq[Expr](e.len)
    for i, it in e.children.pairs:
      elems[i] = eval(it)
    Expr(kind: ekTuple, children: elems)
  of ekLambda:
    # fill in the index of the lambda's enclosing frame
    expr(ekLambda, num($c.frames.high), e[1], e[2])
  of ekLetrec:
    let val = eval(e[1])
    c.frames[^1].vars[e[0].id] = val
    eval(e[2])
  of ekIf:
    if eval(e[0]).kind == ekTrue:
      eval(e[1])
    else:
      eval(e[2])
  of ekMatch:
    var res = Value(kind: ekFail)
    let m = eval(e[0])
    for i in 1..<e.children.len:
      if match(c.frames[^1], e[i][0], m):
        res = eval(e[i][1])
        break

    if res.kind == ekFail:
      raise Failure.newException("") # no match
    res
  of ekTry:
    var res: Expr
    block label:
      try:
        # XXX: hm, why not replace the "success" branch with a functional
        #      value?
        c.frames[^1].vars[e[1].id] = eval(e[0])
      except Failure:
        res = eval(e[3])
        break label
      res = eval(e[2])
    res
  of ekApp:
    let callee = eval(e[0])
    let arg = eval(e[1])
    if callee.kind == ekFunc:
      eval(funcs, c, callee.id, arg)
    elif callee.kind == ekLambda:
      let frame = Frame(parent: parseInt(callee[0].val),
                        vars: toTable({callee[1].id: arg}))
      c.with frame: eval(callee[2])
    else:
      # return the application as is
      expr(ekApp, callee, arg)
  of ekBranch, ekWildcard:
    # TODO: use unreachable
    raise Defect.newException("")
