## Implements the `build` macro, for constructing abstract syntax trees.

import std/[genasts, macros, strformat, tables]
import passes/trees
import nanopass/[asts, helper, nplang, nppatterns]

type
  Candidate = object
    ## Represents a potential form candidate matching the input construction.
    tag: int ## form tag
    types: seq[int]
      ## for each operand in the input construction, the required type
    min: int ## minimum number of items a dynamic operand must have
    max: int ## maximum number of items a dynamic operand can have

proc toPrefix(cand: Candidate, start: int): NimNode =
  ## Turns the type sequence starting at `start` into a prefix (to be used
  ## in a prefix tree).
  # note: for the sake of efficiency, the prefix tree is stored as an
  # AST using a tiny custom grammar
  result = nnkBracket.newTree()
  for i in start..<cand.types.len:
    result.add newIntLitNode(cand.types[i])
  result.add nnkIfExpr.newTree(
    nnkTupleConstr.newTree(
      newIntLitNode(cand.min),
      newIntLitNode(cand.max),
      newIntLitNode(cand.tag)))

proc insert(tree: NimNode, c: Candidate, i=0) =
  ## Inserts `c` into the prefix tree `tree`.
  case tree.kind
  of nnkCurly:
    # try to merge into one of the alternatives
    for it in tree.items:
      if it[0].intVal == c.types[i]:
        insert(it, c, i)
        return
    # a new alternative
    tree.add nnkPar.newTree(
      newIntLitNode(c.types[i]),
      toPrefix(c, i + 1))
  of nnkIfExpr:
    # the guards need to stay ordered by minimum dynamic length
    # (descending) first, and maximum dynamic length
    # (ascending) second
    assert i == c.types.len
    var at = 0
    let tup = nnkTupleConstr.newTree(
      newIntLitNode(c.min),
      newIntLitNode(c.max),
      newIntLitNode(c.tag))
    while at < tree.len:
      let it = tree[at]
      if it[0].intVal.int < c.min or
         (it[0].intVal.int == c.min and it[1].intVal.int > c.max):
        break
      inc at

    tree.insert(at, tup)
  of nnkBracket:
    var i = i
    var j = 0
    while j < tree.len - 1 and tree[j].intVal.int == c.types[i]:
      inc i
      inc j

    if j == tree.len - 1:
      # the sequences are the same so far; merge the tails
      insert(tree[j], c, i)
    else:
      # fork where the sequences start to differ
      let old = nnkBracket.newTree(tree[(j + 1)..^1])
      tree.del(j + 1, tree.len - j - 1)
      tree[j] = nnkCurly.newTree(
        nnkPar.newTree(tree[j], old),
        nnkPar.newTree(newIntLitNode(c.types[i]), toPrefix(c, i + 1)))
  else:
    unreachable()

# ---------- helper routines ----------

{.push stacktrace: off.}

proc lookup[E; M: tuple](): auto {.compileTime.} =
  var x: M
  for it in fields(x):
    when E is typeof(it[0]):
      return it[1]

proc lengthError(len: int) {.noinline.} =
  raise ValueError.newException(
    fmt"no form is able to fit the expanded sequence (length = {len}")

proc append[L, U](ast: var Ast[L, auto], x: Value[U]) =
  ast.tree.nodes.add TreeNode[uint8](
    kind: typeof(lookup[U, L.meta.term_map]()).V,
    val: x.index)

proc append[L](ast: var Ast[L, auto], x: RecordRef) =
  ast.tree.nodes.add TreeNode[uint8](
    kind: typeof(lookup[typeof(x), L.meta.record_map]()).V,
    val: x.id)

proc append[L](ast: var Ast[L, auto], x: Metavar) =
  ast.tree.nodes.add TreeNode[uint8](kind: RefTag, val: uint32(x.index))

proc append[L](ast: var Ast[L, auto], x: openArray) =
  for it in x.items:
    append[L](ast, it)

template coerce[S, T, U](s: S, val: U, _: typedesc[Value[T]]): Value[T] =
  mixin pack
  when T is U:
    Value[T](index: pack(s, val)) # no coercion is necessary
  else:
    Value[T](index: pack(s, T(val))) # try a coercion, an error is fine

{.pop.}

# ---------- macro implementation ----------

proc containsForm(lang: LangInfo, typ: LangType, form: int): bool =
  if form in typ.forms:
    result = true
  else:
    result = false
    for it in typ.sub.items:
      if lang.types[it].kind == tkNonTerminal and
         containsForm(lang, lang.types[it], form):
        result = true
        break

proc buildForm(lang: LangInfo, typ: int, ast, e: NimNode): NimNode

proc buildRecord(lang: LangInfo, ast, e: NimNode): NimNode =
  ## Translates a record construction form from the `build` language
  ## to NimSkull.
  assert e.kind == nnkObjConstr
  let name = e[0].strVal
  let typ = lang.map.getOrDefault(name, -1)
  if typ == -1:
    return makeError(fmt"no meta-variable or record called '{name}' exists",
                     e[0])
  elif lang.types[typ].kind != tkRecord:
    return makeError(fmt"type '{name}' is not a record", e[0])

  let tmp = genSym("")
  let mvar = ident(lang.types[typ].mvar)
  result = newStmtList()
  result.add newVarStmt(tmp, quote do: default(typeof(`ast`.records.`mvar`[0])))
  for i in 1..<e.len:
    let fname = e[i][0].strVal
    let val = e[i][1]
    var ftyp = -1
    for it in lang.types[typ].fields:
      if it.name == fname:
        ftyp = it.typ
        break

    if typ == -1:
      result.add makeError(fmt"'{name}' has no field called '{fname}'",
                           e[i][0])
      continue

    let body =
      case lang.types[ftyp].kind
      of tkTerminal:
        # cannot use genAst because it messes with source locations
        let s = bindSym"coerce"
        let field = ident(fname)
        quote do:
          when `val` is Value:
            `val`
          else:
            `s`(`ast`.storage[], `val`, typeof(`tmp`.`field`))
      of tkRecord:
        if val.kind == nnkSym:
          val # let the compiler report a type mismatch
        else:
          buildRecord(lang, ast, val)
      of tkNonTerminal:
        if val.kind == nnkSym:
          val # let the compiler report a type mismatch
        else:
          buildForm(lang, ftyp, ast, val)

    copyLineInfo(body, val)
    result.add nnkAsgn.newTree(newDotExpr(tmp, ident(fname)), body)

  result.add quote do:
    `ast`.records.`mvar`.add(`tmp`)
    `ast`.L.`mvar`(id: `ast`.records.`mvar`.high.uint32)

proc buildForm(lang: LangInfo, typ: int, ast, e: NimNode): NimNode =
  ## Emits a tree construction for the AST described by `e`, with the syntax
  ## from `lang`.

  # the `build` macro is complex, as:
  # * there may be multiple forms in a language that have the same name
  # * the interpolated operands' types are not known to the macro
  # * list expansion is allowed, at least a single one
  # In effect, a sort of overload resolution has to be performed for picking
  # which form the build syntax ultimately matches. Due to list expansion,
  # this cannot always be known at compile-time, in which case disambiguation
  # has to happen at *run-time*. In the abstract, the macro works by emitting
  # a decision tree (using `when` statements) that selects the form based on
  # the operands' types

  proc newMismatchError(src, dst, info: NimNode): NimNode =
    result = quote do:
      {.error: "expected type fitting " & $`dst` & ", but got " &
               $typeof(`src`).}
    copyLineInfoForTree(result, info)

  proc makeMatch(src, expect: NimNode): NimNode =
    let error = newMismatchError(src, expect, src)
    let append = bindSym"append"
    result = quote do:
      when matches(`src`, `expect`):
        `append`(`ast`, `src`)
      else:
        `error`
    copyLineInfoForTree(result, src)

  proc addAll(to, n: NimNode) =
    if n.kind == nnkStmtList:
      for it in n.items:
        to.add it
    else:
      to.add n

  proc process(lang: LangInfo, typ: LangType, n: NimNode): NimNode {.closure.} =
    ## Parses the expression `n` and interprets in the context of `typ`,
    ## returning either a `when`-then-else statement, a statement list
    ## containing such `when` statement, or, if there's a static type error,
    ## a single error statement.
    case n.kind
    of nnkCall:
      if n[0].kind != nnkIdent:
        error("constructor must be an identifier", n[0])

      case typ.kind
      of tkTerminal:
        # expected a terminal, but the constructor can only be that of a form
        let mvar = ident(typ.mvar)
        result = quote do:
          {.error: "expected '" & $`ast`.L.`mvar` & "', but got form".}
        copyLineInfoForTree(result, n)
        return
      of tkRecord:
        # expected a record, but the constructor can only be that of a form
        let mvar = ident(typ.mvar)
        result = quote do:
          {.error: "expected '" & $`ast`.L.`mvar` & "', but got form".}
        copyLineInfoForTree(result, n)
        return
      of tkNonTerminal:
        discard "all good"

      var candidates: seq[Candidate]

      # gather all forms part of `typ` that have a matching name and whose
      # shape matches that of the construction
      for id, form in lang.forms.pairs:
        if form.name != n[0].strVal or not containsForm(lang, typ, id):
          continue

        var fpos = 0 # position in form description
        var i = 1
        var min, max = 0
        var types = newSeq[int](n.len - 1)
        while i < n.len and fpos < form.elems.len:
          types[i - 1] = form.elems[fpos].typ
          case n[i].kind
          of nnkSym, nnkCall, nnkLiterals:
            # may only be a single element
            if form.elems[fpos].repeat:
              break
            inc fpos
          of nnkBracket:
            # must only appear where a list is expected
            if not form.elems[fpos].repeat:
              break
            inc fpos
          of nnkPrefix:
            # unpack expression. Expands to elements of the exact same type
            if min != 0:
              error("outside a bracket, only a single expansion is allowed",
                    n[i])

            let start = fpos
            let fin = form.elems.len - (n.len - i - 1)
            while fpos < fin and form.elems[fpos].typ == form.elems[start].typ:
              if form.elems[fpos].repeat:
                max = high(int) # expanded list doesn't have a max length
              else:
                min += 1
              inc fpos

            if fpos == start:
              break # fits nothing in the receiving form
          else:
            unreachable(n[i].kind)
          inc i

        if fpos < form.elems.len or i < n.len:
          continue # shape doesn't match

        if max == 0:
          max = min # the expanded list, if any, has a known upper limit

        # shape matches
        candidates.add Candidate(
          tag: form.ntag,
          types: types,
          min: min,
          max: max)

      if candidates.len == 0:
        return
          makeError("form doesn't match any of the productions expected here", n)

      # `process` having a closure context is costly, so pass the necessary
      # local state via an aggregate parameter to `emit`
      type Context = tuple[start, expanded: NimNode]

      proc emit(lang: LangInfo, c: Context, t, n: NimNode, i: int): NimNode =
        ## Given a prefix tree `t` and construction `n` (starting at `i`),
        ## creates a NimSkull statement sequence statically dispatching over
        ## the operands' types to select the right form, intertwined with
        ## appending to the AST.
        case t.kind
        of nnkBracket:
          result = newStmtList()
          for j in 0..<t.len:
            result.add emit(lang, c, t[j], n, i+j)
        of nnkCurly:
          var err: NimNode
          result = nnkWhenStmt.newTree()
          for it in t.items:
            let got = emit(lang, c, it[0], n, i)
            var cond, body: NimNode
            if got.kind == nnkWhenStmt:
              body = got[0][1]
              cond = got[0][0]
            else:
              # lift the first when statement to the top
              for i in 0..<got.len:
                if got[i].kind == nnkWhenStmt:
                  let first = got[i]
                  # replace the when statement with its body
                  got.del(i)
                  got.insert(i, first[0][1])
                  body = got
                  cond = first[0][0]
                  break

            if body.isNil:
              # no guard -> happens when there's a static type error
              err = got
            else:
              body.add emit(lang, c, it[1], n, i+1)
              result.add nnkElifBranch.newTree(cond, body)

          if result.len == 0:
            # none of the variants are viable
            result = err
          else:
            result.add nnkElse.newTree(
              makeError("not a valid production for this position", n[i]))
        of nnkIfExpr:
          proc genBody(ctx: Context, tup: NimNode): NimNode =
            if ctx.start.isNil:
              newStmtList() # the node tag is set already
            else:
              let start = ctx.start
              let id = tup[2]
              quote do: `ast`.tree.nodes[`start`].kind = `id`

          let expanded = c.expanded
          if expanded != nil:
            # only when there's a list to expand can more than one shape of a
            # form statically match for a construction. Run-time disambiguation
            # is required
            result = nnkIfStmt.newTree()
            for it in t.items:
              var cond = ident"true"
              if it[0].intVal == it[1].intVal:
                # no bound check is needed
                let m = it[0]
                cond = quote do: len(`expanded`) == `m`
              else:
                if it[0].intVal > 0:
                  let val = it[0]
                  cond = nnkInfix.newTree(ident"and", cond,
                    quote do: len(`expanded`) >= `val`)
                if it[1].intVal < high(int):
                  let val = it[1]
                  cond = nnkInfix.newTree(ident"and", cond,
                    quote do: len(`expanded`) <= `val`)

              result.add nnkElifExpr.newTree(cond, genBody(c, it))

            if result.len == 1 and result[0][0].kind == nnkIdent:
              # no check is necessary
              result = result[0][1]
            else:
              result.add nnkElse.newTree(
                genAst(expanded) do: lengthError(len(expanded)))
          else:
            result = genBody(c, t[0])
        of nnkIntLit:
          result = process(lang, lang.types[t.intVal], n[i + 1])
        of nnkNilLit:
          result = newStmtList()
        else:
          unreachable()

      proc appendLenExpr(to: var NimNode, n: NimNode, start: int) =
        for i in start..<n.len:
          let x =
            case n[i].kind
            of nnkPrefix:
              let it = n[i][1]
              quote do: len(`it`)
            of nnkBracket:
              to.appendLenExpr(n[i], 0)
              continue
            else:
              quote do: 1

          to = nnkInfix.newTree(ident"+", to, x)

      # first, create a prefix tree out of the candidates' type lists
      var tree = toPrefix(candidates[0], 0)
      for i in 1..<candidates.len:
        insert(tree, candidates[i])

      var lenExpr = newIntLitNode(0)
      lenExpr.appendLenExpr(n, 1)

      var c: Context
      # find the expanded list, if any
      for it in n.items:
        if it.kind == nnkPrefix:
          c.expanded = it[1]
          break

      result = newStmtList()
      if candidates.len == 1:
        # simple case, the tag is known upfront
        let id = candidates[0].tag.uint8
        c.start = nil # no 'start' variable needed
        result.add genAst(ast, id, lenExpr) do:
          ast.tree.nodes.add TreeNode[uint8](kind: id, val: uint32(lenExpr))
      else:
        # the tag is only known at the end
        c.start = genSym("start")
        result.add genAst(ast, start=c.start, lenExpr) do:
          let start = ast.tree.nodes.len
          ast.tree.nodes.add TreeNode[uint8](kind: 0, val: uint32(lenExpr))

      result.addAll emit(lang, c, tree, n, 0)
    of nnkBracket:
      # all operands in the bracket must fit the list's element type
      result = newStmtList()
      for it in n.items:
        result.addAll process(lang, typ, it)
    of nnkPrefix:
      let mvar = ident(typ.mvar)
      result = makeMatch(n[1], (genAst(ast, mvar) do: PArray[ast.L.mvar]))
    else:
      let mvar = ident(typ.mvar)
      case typ.kind
      of tkTerminal:
        let expect = quote do: `ast`.L.`mvar`
        let error = newMismatchError(n, expect, n)
        let append = bindSym"append"
        result = quote do:
          when matches(`n`, `expect`) or `n` is `expect`.T:
            when `n` is `expect`.T:
              `append`(`ast`, terminal(`n`))
            else:
              `append`(`ast`, `n`)
          else:
            `error`
      of tkRecord, tkNonTerminal:
        result = makeMatch(n, (quote do: `ast`.L.`mvar`))

  proc hoist(lang: LangInfo, to, e: NimNode): NimNode =
    ## Hoists all immediate non-form constructions in `e` to `to`.
    case e.kind
    of nnkCall:
      if e[0].strVal in lang.map:
        let id = lang.map[e[0].strVal]
        if lang.types[id].kind != tkTerminal:
          error("only meta-variable ranging over terminal is allowed here", e)

        let mvar = ident(lang.types[id].mvar)
        result = genSym()
        to.add genAst(result, ast, mvar, src=e[1]) do:
          let result = coerce(ast.storage[], src, typeof(ast).L.mvar)
      else:
        result = e
        for i in 1..<e.len:
          e[i] = hoist(lang, to, e[i])
    of nnkObjConstr:
      # record constructions may create their own nodes, hence them
      # having to be hoisted
      result = genSym()
      to.add newLetStmt(result, buildRecord(lang, ast, e))
    of nnkBracket:
      result = e
      for i in 0..<e.len:
        e[i] = hoist(lang, to, e[i])
    else:
      result = e # nothing to do

  let mvar = ident(lang.types[typ].mvar)
  let root = genSym("root")
  result = newStmtList()
  let e = hoist(lang, result, e)
  result.add quote do:
    let `root` = NodeIndex(`ast`.tree.nodes.len)
  result.add process(lang, lang.types[typ], e)
  result.add quote do:
    `ast`.L.`mvar`(index: `root`)

macro buildImpl(lang: static LangInfo, name: static string,
                ast, e: untyped): untyped =
  ## Emits a tree construction for the AST described by `e`, with the syntax
  ## from `lang`.
  let typ = lang.map[name]
  case lang.types[typ].kind
  of tkNonTerminal: buildForm(lang, typ, ast, e)
  of tkRecord:      buildRecord(lang, ast, e)
  of tkTerminal:    unreachable()

macro buildFirstPass(ast, mv, e: untyped): untyped =
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
        if n[i].kind != nnkBracket:
          result[i] = hoist(n[i], list)
        else:
          error("nested bracket syntax is not allowed", n[i])
    of nnkObjConstr:
      n[0].expectKind {nnkIdent, nnkSym}
      # XXX: only identifiers should reach here, but due to compiler bugs
      #      (i.e., input AST mutations) symbols also sometimes make their way here
      result = n
      for i in 1..<n.len:
        n[i].expectKind nnkExprColonExpr
        n[i][0].expectKind nnkIdent
        result[i][1] = hoist(n[i][1], list)
    of nnkPrefix:
      if n[0].strVal == "^":
        # an unquote
        let tmp = genSym()
        copyLineInfo(tmp, n[1])
        list.add newLetStmt(tmp, n[1])
        result = tmp
      elif n[0].strVal == "...":
        # the operand is automatically unquoted
        let tmp = genSym()
        copyLineInfo(tmp, n[1])
        list.add newLetStmt(tmp, n[1])
        result = n
        result[1] = tmp
      else:
        error("unexpected syntax", n)
    of nnkIdent, nnkSym, nnkAccQuoted:
      # auto-unquote as it cannot be anything part of the construction
      let tmp = genSym()
      copyLineInfo(tmp, n)
      list.add newLetStmt(tmp, n)
      result = tmp
    of nnkLiterals - {nnkNilLit}:
      result = n
    else:
      error("unexpected syntax", n)

  let e = hoist(e, result)
  let impl = bindSym"buildImpl"
  result.add quote do:
    `impl`(idef(`mv`.L), `mv`.N, `ast`, `e`)

template build*[L, N](ast: var Ast[L, auto], t: typedesc[Metavar[L, N]],
                      e: untyped): untyped =
  ## Evaluates the AST construction expression `e`, whose result must be a
  ## production of `mv`, returning a `Metavar` pointing to the created AST
  ## fragment.
  buildFirstPass(ast, t, e)

template build*[L, N](ast: var Ast[L, auto], t: typedesc[RecordRef[L, N]],
                      e: untyped): t =
  ## Evaluates the given record construction `e` in the context of `ast`,
  ## returning a reference to the new record.
  buildFirstPass(ast, t, e)
