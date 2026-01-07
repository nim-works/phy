## Implements the `parser <#parser.>`_ macro, for generating an AST parser for
## a language.

import
  std/[genasts, macros, tables],
  experimental/[sexp_parse],
  nanopass/[asts, nplang, helper]

import experimental/sexp {.all.} # we need access to the internal parser

# the core parser logic for a language is implemented in generic routines,
# which themselves call internal macros; the external macro then only expands
# to code calling said generic routines. The benefit: most of the logic for
# parsing an AST is only generated once per language, even when more than one
# parser is generated for a language. This is somewhat problematic for symbol
# binding (for the terminal parsers), however, given how generics work

proc raiseError(line, col: int, msg: string) {.noreturn.} =
  raise ValueError.newException("(" & $line & ", " & $col & ") " & msg)

macro genTerminalParser(lang: static LangInfo) =
  result = newStmtList()
  # emit the terminal handlers
  for it in lang.types.items:
    if it.terminal:
      let typ = ident(it.name)
      let tag = it.ntag.uint8
      result.add quote do:
        block:
          let val = tryParse(node, `typ`)
          if val.isSome:
            return TreeNode[uint8](kind: `tag`, val: pack(lit, val.unsafeGet))

proc parseTerminal[L, S](lit: var S, node: SexpNode, line, col: int): TreeNode[uint8] =
  ## Implements fallback parsing of terminals.
  mixin idef
  genTerminalParser(idef(L))
  raiseError(line, col,
    "'" & $node & "' is neither a valid language form nor terminal")

proc parse[L, S](p: var SexpParser, to: var Ast[L, S])

proc rawParseForm[L, S](p: var SexpParser, to: var Ast[L, S]) =
  ## Parses and appends the elements for a form, without performing any
  ## grammar checks.
  let start = to.tree.nodes.len
  to.tree.nodes.add TreeNode[uint8]() # sub-tree node
  var len = 0
  while p.currToken != tkParensRi:
    parse(p, to)
    space(p)
    inc len

  discard getTok(p) # eat the parens
  to.tree.nodes[start].val = uint32(len)
  # the tag is computed separately

macro parseFormImpl(lang: static LangInfo) =
  ## Expands to the form parser for `lang`.

  # to keep the implementation simple, subtrees are parsed without regard
  # to grammar at first. Once a subtree is fully parsed, the grammar check
  # takes place and - if the check succeeds - a form tag is assigned to
  # the node

  proc mergeInto(m, into: NimNode): NimNode =
    ## Merges match expression `m` into `into`.
    proc mustTrail(n: NimNode): bool =
      n[0].kind == nnkEmpty or n[1].intVal <= 0

    case into.kind
    of nnkCurly:
      for i, it in into.pairs:
        if it[0] == m[0]: # same head?
          into[i] = mergeInto(m, into[i])
          return into
        elif mustTrail(it) and not mustTrail(m):
          into.insert i, m
          return into

      into.add m
      into
    of nnkCall:
      if m[0] == into[0]:
        # same head
        into[^1] = mergeInto(m[^1], into[^1])
        into
      elif mustTrail(into):
        # an 'else' always comes last
        nnkCurly.newTree(m, into)
      else:
        nnkCurly.newTree(into, m)
    else:
      unreachable()

  proc translate(lang: LangInfo, m: NimNode): NimNode =
    ## Translates the match expression from the mini-language to NimSkull code.
    case m.kind
    of nnkIntLit:
      result = quote do:
        to.tree.nodes[start].kind = `m`
    of nnkCurly:
      result = nnkIfStmt.newTree()
      for it in m.items:
        let sub = translate(lang, it)
        if sub.kind == nnkIfStmt:
          result.add sub[0]
        else:
          result.add nnkElse.newTree(sub)
    of nnkCall:
      let head = m[0]
      let raiseErr = bindSym"raiseError"
      let next = translate(lang, m[^1])
      if head.kind == nnkEmpty:
        # matches at the end of the sub-tree
        result = quote do:
          if cursor.int == to.tree.nodes.len:
            `next`
          else:
            `raiseErr`(line, col, "end of sub-tree expected, but got more nodes")
      else:
        let tags = nnkCurly.newTree()
        let name = lang.types[head.intVal].name
        if lang.types[head.intVal].terminal:
          tags.add newLit(uint8(lang.types[head.intVal].ntag))
        else:
          for it in ntags(lang, lang.types[head.intVal]):
            tags.add newLit(uint8(it))

        if m[1].intVal == 1: # single item?
          result = quote do:
            if cursor.int < to.tree.nodes.len and
               to.tree[cursor].kind in `tags`:
              cursor = to.tree.next(cursor)
              `next`
            else:
              `raiseErr`(line, col, "expected production of '" & `name` & "'")
        else:
          # a list; may be comprised of zero or more items
          let bias = -m[1].intVal
          result = quote do:
            for i in uint32(`bias`)..<to.tree.nodes[start].val:
              if to.tree[cursor].kind in `tags`:
                cursor = to.tree.next(cursor)
              else:
                `raiseErr`(line, col, "expected " & `name`)
            `next`
    else:
      unreachable()

  result = nnkCaseStmt.newTree(ident"name")

  var buckets: Table[string, seq[int]]
  for i, form in lang.forms.pairs:
    buckets.mgetOrPut(form.name, @[]).add i

  for name, forms in buckets.pairs:
    var m: NimNode # the match expression

    # in order to produce some more helpful error message, the generated code is
    # structured such that it also know *where* a grammar violation is, not
    # just that there is one

    for id in forms.items:
      var top, prev = NimNode nil
      # generate the match expression for the form...
      for it in lang.forms[id].elems:
        let got = nnkCall.newTree(newIntLitNode(it.typ))
        if it.repeat:
          got.add newIntLitNode(-(lang.forms[id].elems.len - 1))
        else:
          got.add newIntLitNode(1)
        if top.isNil:
          top = got
          prev = got
        else:
          prev.add got
          prev = got

      let last = nnkCall.newTree(
        newEmptyNode(),
        newEmptyNode(),
        newIntLitNode(lang.forms[id].ntag))
      if top.isNil:
        top = last
      else:
        prev.add last

      # ... and merge it into the combined one
      if m.isNil:
        m = top
      else:
        m = mergeInto(top, m)

    # emit the code for the form parser(s)
    result.add nnkOfBranch.newTree(newStrLitNode(name), newStmtList(
      (quote do:
        let start = to.tree.nodes.len
        var cursor {.used.} = NodeIndex(start + 1)),
      newCall(bindSym"rawParseForm", ident"p", ident"to"),
      translate(lang, m)))

  # emit the terminal parsing fallback
  result.add nnkElse.newTree(
    genAst(to=ident"to", p=ident"p", lang=ident"L", name=ident"name") do:
      var node = newSList(newSSymbol(name))
      while p.currToken != tkParensRi:
        node.add parseSexp(p)
        space(p)
      discard getTok(p)
      to.tree.nodes.add parseTerminal[lang](to.storage[], node, line, col)
  )

proc parseForm[L, S](p: var SexpParser, to: var Ast[L, S],
                     name: string, line, col: int) =
  ## Tries to parse an AST form with name `name` from `p`, falling back to
  ## terminal parsing if no form with the given name exists in `L`.
  parseFormImpl(idef(L))

proc parse[L, S](p: var SexpParser, to: var Ast[L, S]) =
  ## Parses a production from `p` at the current position.
  if p.currToken == tkParensLe:
    # could be both a form or terminal
    let (line, col) = (p.getLine(), p.getColumn())
    let tok = getTok(p)
    space(p)
    if tok == tkSymbol:
      let name = captureCurrString(p)
      discard getTok(p)
      space(p)
      parseForm(p, to, name, line, col)
    else:
      raiseParseErr(p, "expected a symbol")
  else:
    # parse an S-expression and have the user-provided parser figure it out
    let (line, col) = (p.getLine(), p.getColumn())
    to.tree.nodes.add parseTerminal[L](to.storage[], parseSexp(p), line, col)

macro check(lang: static LangInfo, nterm: static string,
            ast, pos, line, col: untyped) =
  ## Makes sure the production at `pos` is one of the non-terminal identified
  ## by `nterm`, raising an error if not.
  var se = nnkCurly.newTree()
  for it in ntags(lang, lang.types[lang.map[nterm]]):
    se.add newLit(uint8(it))

  genAst(ast, pos, se, nterm, line, col) do:
    if ast.tree.nodes[pos].kind notin se:
      raiseError(line, col,
        "expected production of non-terminal '" & nterm & "'")

macro parser*(def: untyped) =
  ## Procedure macro that generates a parser for a language's AST. The return
  ## type is changed to be a tuple of an AST plus the original return type,
  ## which must be a reference to one of the target language's non-terminals.
  if def.kind != nnkProcDef:
    error("'parser' must be applied to a procdef", def)
  if def.body.kind != nnkEmpty:
    error("'parser' must be applied to a prototype", def.name)
  if def.params.len != 2 or def.params[1].len != 3:
    error("prototype must have a single parameter", def.name)

  result = def
  let typ = def.params[0]
  let param = def.params[1][0]
  let err = makeError("parameter must be of type `var SexpParser`", param)

  result.params[0] = quote do:
    (Ast[`typ`.L, Literals], `typ`)
  result.body = genAst(res=ident"result", param, err, typ):
    when param isnot SexpParser:
      err
    res[0].storage = new(typeof(res[0].storage))

    let (line, col) = (param.getLine(), param.getColumn())
    parse(param, res[0])
    check(idef(typ.L), typ.N, res[0], 0, line, col)
