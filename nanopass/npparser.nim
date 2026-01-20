## Implements the routines for parsing S-expression-based AST representation
## into ASTs.

import
  std/[genasts, macros, strutils, tables, typetraits],
  experimental/[sexp_parse],
  nanopass/[asts, nplang]

import experimental/sexp {.all.} # we need access to the internal parser

type
  Ctx[L, S] = object
    # accumulators:
    tree: typeof(Ast[L, S].tree)
    records: typeof(Ast[L, S].records)
    storage: ref S
    staging: typeof(Ast[L, S].tree)
      ## staging buffer for out-of-band trees embedded in records
    # additional parsing state:
    maps: array[tupleLen(L.meta.records), Table[int, uint32]]
      ## for each record type, keeps track of the declared ID -> real ID
      ## mappings
    locs: seq[SLocRef]
      ## stack of source locations
    curSLoc: SLocRef
      ## source location to use for parsed nodes

macro mapTypeImpl(lang: static LangInfo, lname, typ: untyped): int =
  result = nnkWhenStmt.newTree()
  for i, it in lang.types.pairs:
    result.add nnkElifBranch.newTree(
      newCall(ident"is", typ, newDotExpr(lname, ident(it.mvar))),
      newIntLitNode(i))

  result.add nnkElse.newTree(quote do: {.error: "unreachable".})

proc mapType[L, T](): int {.compileTime.} =
  ## Maps the type `T` to the integer IDs identifying it in `L`.
  mapTypeImpl(idef(L), L, T)

macro tags(lang: static LangInfo, typ: static int): set[uint8] =
  ## Returns the node tags for the productions inhabiting `typ`.
  case lang.types[typ].kind
  of tkRecord:
    nnkCurly.newTree(newLit(uint8 lang.types[typ].rtag))
  of tkTerminal:
    nnkCurly.newTree(newLit(uint8 lang.types[typ].ntag))
  of tkNonTerminal:
    var se = nnkCurly.newTree()
    for it in ntags(lang, lang.types[typ]):
      se.add newLit(uint8 it)
    se

proc eatString(p: var SexpParser): string =
  if p.isTok(tkString):
    result = captureCurrString(p)
    discard getTok(p)
  else:
    raiseParseErr(p, "expected string")

proc eatInt(p: var SexpParser): int =
  if p.isTok(tkInt):
    result = parseInt(currString(p))
    discard getTok(p)
  else:
    raiseParseErr(p, "expected integer")

proc raiseError(line, col: int, msg: string) {.noreturn.} =
  raise ValueError.newException("(" & $line & ", " & $col & ") " & msg)

template check[L](c: Ctx[L, auto], pos: NodeIndex, line, col: int,
                  t: typedesc) =
  ## Makes sure the production at `pos` is one part of the non-terminal
  ## identified by `nterm`, raising an error if not.
  if c.tree[pos].tag notin tags(idef(typeof(L)), mapType[L, t]()):
    when t is Production:
      raiseError(line, col,
        "expected production of '" & t.N & "'")
    else:
      raiseError(line, col,
        "expected '" & $t & "'")

macro parseTerminalImpl(lang: static LangInfo) =
  result = newStmtList()
  # emit the terminal handlers
  for it in lang.types.items:
    if it.kind == tkTerminal:
      let typ = ident(it.name)
      let tag = it.ntag.uint8
      result.add quote do:
        block:
          let val = tryParse(node, `typ`)
          if val.isSome:
            return node(`tag`, c.curSLoc, pack(c.storage[], val.unsafeGet))

proc parseTerminal[L, S](c: var Ctx[L, S], node: SexpNode,
                         line, col: int): AstNode =
  ## Implements fallback parsing of terminals.
  mixin idef
  parseTerminalImpl(idef(L))
  raiseError(line, col,
    "'" & $node & "' is neither a valid language form nor terminal")

proc parse[L, S](c: var Ctx[L, S], p: var SexpParser)

proc extract(c: var Ctx, to: var Production, pos: int) =
  # move the sub-tree over to the out-of-band storage
  let start = c.staging.nodes.len
  let count = c.tree.nodes.len - pos
  c.staging.nodes.setLen(start + count)
  copyMem(addr c.staging.nodes[start], addr c.tree.nodes[pos],
          sizeof(AstNode) * count)
  c.tree.nodes.shrink(pos)
  to.index = NodeIndex(start)

proc extract(c: var Ctx, to: var RecordRef, pos: int) =
  to.id = c.tree.nodes.pop().val

proc extract(c: var Ctx, to: var Value, pos: int) =
  to.id = c.tree.nodes.pop().val

proc parseFieldsImpl[L](c: var Ctx[L, auto], p: var SexpParser,
                        tup: var tuple) =
  ## Parses the body of a record-def and fills `tup` with the values.
  for name, it in fieldPairs(tup):
    let start = c.tree.nodes.len
    space(p)
    eat(p, tkParensLe)
    if currString(p) != name:
      raiseParseErr(p, "expected '" & name & "'")
    discard getTok(p)
    space(p)

    # parse the field's value...
    parse(c, p)
    # ...then make sure its type is correct
    check(c, NodeIndex(start), p.getLine(), p.getColumn(), typeof(it))

    extract(c, it, start)
    space(p)
    eat(p, tkParensRi)

macro parseFields(lang: static LangInfo, c: var Ctx, name: string) =
  ## Selects the record type based on the dynamic value of `name`, parses
  ## the record's fields, registers the resulting record with `c`, and
  ## appends a record reference to the AST.
  result = nnkCaseStmt.newTree(name)
  var i = 0 # index of the record type
  for typ in lang.types.items:
    if typ.kind == tkRecord:
      let mvar = ident(typ.mvar)
      let tag = typ.rtag
      result.add nnkOfBranch.newTree(newStrLitNode(typ.name),
        genAst(c, mvar, i, tag) do:
          if isDef:
            # records may be recursive, so reserve and remember a slot first
            let slot = c.records.mvar.len
            c.records.mvar.setLen(slot + 1)
            if id in c.maps[i]:
              raiseError(start[0], start[1],
                "a record with the given ID has been defined already")
            c.maps[i][id] = uint32(slot)

            var tup: typeof(c.records.mvar[0])
            parseFieldsImpl(c, p, tup)
            c.records.mvar[slot] = tup
            c.tree.nodes.add node(uint8(tag), uint32(slot))
          else:
            c.maps[i].withValue id, val:
              c.tree.nodes.add node(uint8(tag), val[])
            do:
              raiseError(start[0], start[1],
                "record with ID " & $id & " is missing")
      )
      inc i

  result.add nnkElse.newTree(genAst(name) do:
    raiseError(start[0], start[1],
      "there's no symbol type called '" & name & "'")
  )

proc parseRecord[L, S](c: var Ctx[L, S], p: var SexpParser, isDef: bool) =
  ## Parses a record definition (if `isDef` is true) or reference from `p`.
  space(p)
  let start {.used.} = (p.getLine(), p.getColumn())
  if p.currToken != tkSymbol:
    raiseParseErr(p, "expected symbol")
  let name = captureCurrString(p)
  discard getTok(p)
  space(p)
  let id {.used.} = eatInt(p)

  parseFields(idef(L), c, name)

proc parseMeta[L, S](c: var Ctx[L, S], p: var SexpParser) =
  ## Parses a meta-expression.
  assert p.currToken == tkKeyword
  case currString(p)
  of ":record-def":
    discard getTok(p)
    parseRecord(c, p, true)
  of ":record":
    discard getTok(p)
    parseRecord(c, p, false)
  of ":info":
    # use the given source location for a tree
    discard getTok(p)
    c.locs.add c.curSLoc
    space(p)
    eat(p, tkParensLe)
    let file = eatString(p)
    space(p)
    let startLine = eatInt(p)
    space(p)
    let startCol = eatInt(p)
    space(p)
    if p.currToken == tkParensRi:
      # only a line-column pair
      c.curSLoc = newSourceLoc(c.storage[], file, startLine, startCol)
    else:
      let endLine = eatInt(p)
      space(p)
      let endCol = eatInt(p)
      space(p)
      c.curSLoc =
        newSourceLoc(c.storage[], file, startLine, startCol, endLine, endCol)

    eat(p, tkParensRi)
    space(p)
    parse(c, p)
    c.curSLoc = c.locs.pop()
  of ":no-info":
    # use no source location for a tree
    discard getTok(p)
    space(p)
    c.locs.add c.curSLoc
    c.curSLoc = NoSLoc
    parse(c, p)
    c.curSLoc = c.locs.pop()
  else:
    raiseParseErr(p, "expected meta-expression")

  space(p)
  eat(p, tkParensRi)

proc rawParseForm[L, S](c: var Ctx[L, S], p: var SexpParser) =
  ## Parses and appends the elements for a form, without performing any
  ## grammar checks.
  let start = c.tree.nodes.len
  c.tree.nodes.add node(0, c.curSLoc, 0) # sub-tree node
  var len = 0
  while p.currToken != tkParensRi:
    parse(c, p)
    space(p)
    inc len

  discard getTok(p) # eat the parens
  c.tree.nodes[start].val = uint32(len)
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
        c.tree.nodes[start].tag = `m`
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
          if cursor.int == c.tree.nodes.len:
            `next`
          else:
            `raiseErr`(line, col, "end of sub-tree expected, but got more nodes")
      else:
        let tags = nnkCurly.newTree()
        let name = lang.types[head.intVal].name
        case lang.types[head.intVal].kind
        of tkTerminal:
          tags.add newLit(uint8(lang.types[head.intVal].ntag))
        of tkRecord:
          tags.add newLit(uint8(lang.types[head.intVal].rtag))
        of tkNonTerminal:
          for it in ntags(lang, lang.types[head.intVal]):
            tags.add newLit(uint8(it))

        if m[1].intVal == 1: # single item?
          result = quote do:
            if cursor.int < c.tree.nodes.len and
               c.tree[cursor].tag in `tags`:
              cursor = c.tree.next(cursor)
              `next`
            else:
              `raiseErr`(line, col, "expected production of '" & `name` & "'")
        else:
          # a list; may be comprised of zero or more items
          let bias = -m[1].intVal
          result = quote do:
            for i in uint32(`bias`)..<c.tree.nodes[start].val:
              if c.tree[cursor].tag in `tags`:
                cursor = c.tree.next(cursor)
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

    # in order to produce a more helpful error message, the generated code is
    # structured such that it also knows *where* a grammar violation is, not
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
        let start = c.tree.nodes.len
        var cursor {.used.} = NodeIndex(start + 1)),
      newCall(bindSym"rawParseForm", ident"c", ident"p"),
      translate(lang, m)))

  # emit the terminal parsing fallback
  result.add nnkElse.newTree(
    genAst(c=ident"c", p=ident"p", name=ident"name") do:
      var node = newSList(newSSymbol(name))
      while p.currToken != tkParensRi:
        node.add parseSexp(p)
        space(p)
      discard getTok(p)
      c.tree.nodes.add parseTerminal(c, node, line, col)
  )

proc parseForm[L, S](c: var Ctx[L, S], p: var SexpParser,
                     name: string, line, col: int) =
  ## Tries to parse an AST form with name `name` from `p`, falling back to
  ## terminal parsing if no form with the given name exists in `L`.
  parseFormImpl(idef(L))

proc parse[L, S](c: var Ctx[L, S], p: var SexpParser) =
  ## Parses a production from `p`, raising an error when there's a syntax
  ## error, or when the production is illformed.
  if p.currToken == tkParensLe:
    # could be both a form or terminal
    let (line, col) = (p.getLine(), p.getColumn())
    let tok = getTok(p)
    space(p)
    case tok
    of tkSymbol:
      let name = captureCurrString(p)
      discard getTok(p)
      space(p)
      parseForm(c, p, name, line, col)
    of tkKeyword:
      parseMeta(c, p)
    else:
      raiseParseErr(p, "expected a symbol")
  else:
    # parse an S-expression and have the user-provided parser figure it out
    let (line, col) = (p.getLine(), p.getColumn())
    c.tree.nodes.add parseTerminal(c, parseSexp(p), line, col)

proc parseAst*[S, L, N](p: var SexpParser, T: typedesc[Production[L, N]]
                       ): (Ast[L, S], T) =
  ## Parses the S-expression-based AST representation from `p` into an `Ast`,
  ## returning the result, or - in case of an error - raising an exception.
  var c: Ctx[L, S]
  c.storage = new S

  let (line, col) = (p.getLine(), p.getColumn())
  parse(c, p)
  check(c, NodeIndex(0), line, col, T)

  # append the staging buffer to the main buffer and update the references
  # in `c.records`
  let pos {.used.} = c.tree.nodes.len
  c.tree.nodes.add c.staging.nodes

  for recs in fields(c.records):
    for it in recs.mitems:
      for f in fields(it):
        when f is Production:
          f.index = NodeIndex(pos + ord(f.index))

  result = (
    Ast[L, S](tree: c.tree, records: c.records, storage: c.storage),
    T(index: NodeIndex(0))
  )
