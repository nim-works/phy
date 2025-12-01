## Implements the `build` macro, for constructing abstract syntax trees.

import std/[genasts, macros, strformat, tables]
import passes/trees
import nanopass/[asts, helper, nplang, nplangdef, nppatterns]

proc lookup[E; M: tuple](): auto {.compileTime.} =
  var x: M
  for it in fields(x):
    when E is typeof(it[0]):
      return it[1]

proc append[L, U](to: var PackedTree[uint8], x: Value[U]) =
  to.nodes.add TreeNode[uint8](
    kind: typeof(lookup[U, L.meta.term_map]()).V,
    val: x.index)

proc append[L](to: var PackedTree[uint8], x: Metavar) =
  to.nodes.add TreeNode[uint8](kind: RefTag, val: uint32(x.index))

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
      let cons = n[1]
      test.add quote do:
        let `sym` = Value[`valueType`](index: pack(storage, `cons`))
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
