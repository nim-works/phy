## Implements the high and low-level `match` macros.

import std/[macros, intsets, strformat, tables]
import passes/trees
import nanopass/[asts, helper, nplang]

proc ntags*(lang: LangInfo, typ: LangType): seq[int] =
  ## Returns a list with all possible node tags productions of `typ` can have.
  for it in typ.forms.items:
    result.add lang.forms[it].ntag

  for it in typ.sub.items:
    if lang.types[it].terminal:
      result.add lang.types[it].ntag
    else:
      result.add ntags(lang, lang.types[it])

proc matchImpl*(lang: LangInfo, src: int, ast, sel, rules: NimNode
               ): (seq[NimNode], IntSet) =
  ## Implements the core of the `match` macro:
  ## 1. makes sure the syntax is correct
  ## 2. makes sure the used patterns are unique
  ## 3. generates a sequence of transformed 'of' branches, plus a set storing
  ##    the used forms' tags
  var used: IntSet
    ## covered form productions (identified by ntag)

  # should nested matching (e.g., ``A(x, B(y))``) be desired, `matchImpl`
  # should be factored into two macros macros applied sequentially:
  # 1. the first macro does type checking, producing a type form
  # 2. the second macro translates the typed form into case/if statements
  # combining both steps into one is simple enough when there are no nested
  # patterns, but not otherwise

  proc parseVar(n: NimNode): (string, string) =
    n.expectKind nnkIdent
    let name = n.strVal
    var e = name.high
    # to get the name of the var, trim trailing numbers and a single underscore
    while e >= 0 and name[e] in {'0'..'9'}:
      dec e

    if e >= 0 and name[e] == '_':
      dec e

    result[0] = name[0..e]
    result[1] = name

  proc processIdentPattern(lang: LangInfo, n: NimNode): (NimNode, NimNode) =
    n.expectKind nnkIdent
    let (v, nameStr) = parseVar(n)
    if v notin lang.map:
      error(fmt"no meta-variable with name '{v}'", n)
    let id = lang.map[v]
    if id notin lang.types[src].sub:
      error(fmt"'{v}' is not an immediate production of '{lang.types[src].name}'", n)

    var check, binds: NimNode
    let name = ident(nameStr)
    if lang.types[id].terminal:
      let typ = ident(lang.types[id].name)
      let tag = lang.types[id].ntag
      used.incl(tag)
      # let the compiler report an error for duplicate case labels
      check = newIntLitNode(tag)
      copyLineInfo(check, n)
      binds = newLetStmt(name, quote do: Value[`typ`](index: `ast`[`sel`].val))
    else:
      # the pattern binds a non-terminal
      let typ = ident(v)
      check = nnkCurly.newTree()
      let tags = ntags(lang, lang.types[id])
      for tag in tags.items:
        check.add nnkConv.newTree(ident"uint8", newIntLitNode(tag))
      # mark the first tag as used, to signal that the non-terminal is handled
      used.incl(tags[0])

      copyLineInfoForTree(check, n)
      binds = newLetStmt(name, quote do: src.`typ`(index: `sel`))

    result = (check, binds)

  proc processPattern(lang: LangInfo, n: NimNode): (NimNode, NimNode) =
    case n.kind
    of nnkCall:
      n[0].expectKind nnkIdent
      # parse the pattern:
      var elems = newSeq[tuple[src, dst, name: string]](n.len - 1)
      for i in 1..<n.len:
        case n[i].kind
        of nnkIdent:
          let (v, name) = parseVar(n[i])
          if v notin lang.map or lang.types[lang.map[v]].name == v:
            error(fmt"no metavar named {v}", n[i])
          elems[i - 1] = (v, "", name)
        of nnkBracket:
          n[i].expectLen 1
          let (v, name) = parseVar(n[i][0])
          # cannot check whether the metavar exists. If it doesn't, the
          # compiler will complain with a not-so-helpful error
          elems[i - 1] = ("", v, name)
        else:
          error("unexpected syntax", n)

      # TODO: enforce during language constructions that there are no two
      #       productions that use the same ntag
      var idx = -1
      block search:
        # find a production that matches the pattern:
        for it in lang.types[src].forms.items:
          block form:
            if lang.forms[it].elems.len == elems.len and
               lang.forms[it].name == n[0].strVal:
              for j in 0..<elems.len:
                if elems[j].src != "" and
                   lang.forms[it].elems[j].typ != lang.map[elems[j].src]:
                  # different types, no match
                  break form
                # the `[...]` syntax (i.e., no source type) matches everything
              # found a matching form
              idx = it
              break search
        error(fmt"no production of '{src}' matches the pattern", n)

      let tag = lang.forms[idx].ntag
      let check = newIntLitNode(tag)
      copyLineInfo(check, n)

      # let the compiler report a duplicate case label error
      used.incl(tag)

      if lang.forms[idx].elems.len == 0:
        # form with no elements; nothing to bind
        return (check, newStmtList())

      var binds = newStmtList()
      var cursor = genSym("c")
      binds.add newVarStmt(cursor, quote do: `ast`.child(`sel`, 0))

      # create the check and the bindings
      for i, it in lang.forms[idx].elems.pairs:
        let p = n[i + 1] ## the pattern expression
        let origin = newDotExpr(ident"src", ident(lang.types[it.typ].mvar))
        let target = newDotExpr(ident"dst"):
          if elems[i].dst.len > 0: ident(elems[i].dst)
          else:                    ident(lang.types[it.typ].mvar)
        if it.repeat:
          let bias = lang.forms[idx].elems.len - 1
          if p.kind == nnkIdent:
            # just bind a child slice to the identifier
            binds.add newLetStmt(p, quote do:
              slice[`origin`](`cursor`, uint32(`ast`.len(`sel`) - `bias`)))
            binds.add quote do:
              for _ in 0..<`ast`.len(`sel`)-`bias`:
                `cursor` = `ast`.next(`cursor`)
          else:
            # run the selected transformer on all relevant child nodes and
            # store the result in a seq
            let tmp = genSym()
            binds.add newVarStmt(tmp,
              quote do: newSeq[`target`](`ast`.len(`sel`)-`bias`))
            let callee = ident"->"
            binds.add quote do:
              for i in 0..<`ast`.len(`sel`)-`bias`:
                `tmp`[i] = `callee`(`origin`(index: `cursor`), `target`)
                `cursor` = `ast`.next(`cursor`)
            binds.add newLetStmt(p[0], tmp)
        else:
          # simple case: a single node
          if p.kind == nnkIdent:
            if lang.types[it.typ].terminal:
              binds.add newLetStmt(p, quote do: `origin`(index: `ast`[`cursor`].val))
            else:
              binds.add newLetStmt(p, quote do: `origin`(index: `cursor`))
          else:
            if lang.types[it.typ].terminal:
              binds.add makeError("cannot invoke auto-procesor for terminal", p)
            else:
              binds.add newLetStmt(p[0],
                newCall(ident"->",
                  nnkObjConstr.newTree(origin,
                    nnkExprColonExpr.newTree(ident"index", cursor)),
                  target))
          binds.add quote do:
            `cursor` = `ast`.next(`cursor`)
      result = (check, binds)
    of nnkIdent:
      # must be a terminal/non-terminal meta-var
      result = processIdentPattern(lang, n)
    else:
      error("unexpected syntax", n)

  var branches: seq[NimNode]
  for it in rules.items:
    case it.kind
    of nnkOfBranch:
      it.expectLen 2
      let (check, binds) = processPattern(lang, it[0])
      branches.add nnkOfBranch.newTree(check, newStmtList(binds, it[1]))
    of nnkElse:
      # as a guard against malformed run-time inputs, use an 'of' instead
      # of an 'else' branch
      var ofb = nnkOfBranch.newTree()
      # add all remaining forms:
      for it in lang.types[src].forms.items:
        if not containsOrIncl(used, lang.forms[it].ntag):
          ofb.add newIntLitNode(lang.forms[it].ntag)
      # also include the tags for sub non-terminals and terminals:
      for it in lang.types[src].sub.items:
        if lang.types[it].terminal:
          if not containsOrIncl(used, lang.types[it].ntag):
            ofb.add newIntLitNode(lang.types[it].ntag)
        else:
          let tags = ntags(lang, lang.types[it])
          if not containsOrIncl(used, tags[0]):
            for tag in tags.items:
              ofb.add newIntLitNode(tag)

      if ofb.len == 0:
        # all forms are handled already. Add an 'else' branch before the
        # programmer-provided one so that the compiler can report an
        # "unreachable" warning
        branches.add nnkElse.newTree(newCall(ident"unreachable"))
        branches.add it
      else:
        copyLineInfo(ofb, it)
        ofb.add it[0]
        branches.add ofb
    else:
      error("expected 'of' or 'else'", it)

  result = (branches, used)


macro matchImpl(lang: static LangInfo, nterm: static string,
                ast: PackedTree[uint8], sel: NodeIndex, info: untyped,
                rules: varargs[untyped]): untyped =
  ## The internal implementation `match` dispatches to.
  let (branches, used) = matchImpl(lang, lang.map[nterm], ast, sel, rules)
  result = nnkCaseStmt.newTree(quote do: `ast`[`sel`].kind)
  copyLineInfoForTree(result, info)
  result.add branches
  # add a default handler when all possible productions are covered
  var allCovered = true
  for it in lang.types[lang.map[nterm]].sub.items:
    if lang.types[it].terminal:
      if lang.types[it].ntag notin used:
        allCovered = false
        break
    elif lang.forms[lang.types[it].forms[0]].ntag notin used:
      allCovered = false
      break

  if allCovered:
    result.add nnkElse.newTree(newCall(ident"unreachable"))

template match*(ast: PackedTree[uint8], nt: Metavar,
                branches: varargs[untyped]): untyped =
  ## Provides a convenient way to destructure an AST. Meant to be used as
  ## follows:
  ##
  ## .. code-block:: nim
  ##
  ##   match ast, n:
  ##   of ...: discard
  ##   of ...: discard
  ##   else:   discard
  bind matchImpl
  let idx = nt.index
  matchImpl(idef(typeof(nt).L), typeof(nt).N, ast, idx, nt, branches)
