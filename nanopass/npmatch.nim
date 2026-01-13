## Implements the high and low-level `match` macros.

import std/[macros, intsets, strformat, tables]
import nanopass/[asts, helper, nplang]

type
  FillProc* = proc(lang: LangInfo, idx: int, n, info: NimNode): NimNode
    ## Type for form or type fill callback.
  ExpandConfig* = object
    fillForm*: FillProc
      ## called for filling-in the handling of forms. May be nil
    fillType*: FillProc
      ## called for filling-in the handling of types. May be nil

proc defaultFillForm(lang: LangInfo, idx: int, n, info: NimNode): NimNode =
  makeError(fmt"missing rule for '{render(lang, lang.forms[idx])}'", info)

proc defaultFillType(lang: LangInfo, idx: int, n, info: NimNode): NimNode =
  makeError(fmt"missing rule for '{lang.types[idx].name}'", info)

proc parseVar(n: NimNode): string =
  n.expectKind nnkIdent
  let name = n.strVal
  var e = name.high
  # to get the name of the var, trim trailing numbers and a single underscore
  while e >= 0 and name[e] in {'0'..'9'}:
    dec e

  if e >= 0 and name[e] == '_':
    dec e

  result = name[0..e]

proc fits(lang: LangInfo, a, b: int): bool =
  ## Computes whether type with id `a` can appear where a type with id `b`
  ## is expected.
  if a == b:
    result = true
  elif lang.types[b].kind == tkNonTerminal:
    for it in lang.types[b].sub.items:
      if fits(lang, a, it):
        return true

proc countTags(lang: LangInfo, typ: LangType): int =
  result = typ.forms.len
  for it in typ.sub.items:
    case lang.types[it].kind
    of tkTerminal, tkRecord:
      result += 1
    of tkNonTerminal:
      result += countTags(lang, lang.types[it])

proc containsForm(lang: LangInfo, typ: LangType, fid: int): bool =
  case typ.kind
  of tkNonTerminal:
    if fid in typ.forms:
      true
    else:
      for it in typ.sub.items:
        if containsForm(lang, lang.types[it], fid):
          return true
      false
  of tkTerminal, tkRecord:
    false

proc makeTyped(e, typ, info: NimNode): NimNode =
  typ.copyLineInfo(info) # the type tree carries the source location
  nnkExprColonExpr.newTree(e, typ)

proc fitTo(lang: LangInfo, typ: int, pat: NimNode): NimNode =
  ## Fits a non-'...' typed pattern to the given type, returning either the
  ## fitted pattern or nil.

  proc canMerge(n, into: NimNode): bool =
    assert n.kind == into.kind and n.kind == nnkCall
    result = true
    for i in 1..<n.len:
      if n[i][1] != into[i][1]: # same type?
        result = false
        break

  proc makeConv(e: NimNode, typ: int): NimNode =
    assert e.kind == nnkExprColonExpr
    makeTyped(nnkConv.newTree(e), newIntLitNode(typ), e[1])

  case pat[1].kind
  of nnkEmpty:
    result = pat # stays as is; don't infer
  of nnkNilLit:
    # the type is inferred from the receiver
    result = makeTyped(pat[0], newIntLitNode(typ), pat[1])
  of nnkCurly:
    if lang.types[typ].kind in {tkTerminal, tkRecord}:
      return nil # terminals cannot host any form (they're terminal)

    # filter out the forms not part of the target type and try to merge the
    # remaining ones
    result = nil
    for sub in pat[0].items:
      if containsForm(lang, lang.types[typ], sub[1][0].intVal.int):
        if result.isNil:
          result = makeTyped(sub[0], copyNimTree(sub[1]), sub[1])
        elif canMerge(sub[0], result[0]):
          result[1].add sub[1][0]
        else:
          result = nil # forms cannot be unified
          break

    if result != nil and countTags(lang, lang.types[typ]) != result[1].len:
      result = makeConv(result, typ)
  of nnkIntLit:
    if pat[1].intVal.int == typ:
      result = pat
    elif fits(lang, pat[1].intVal.int, typ):
      result = makeConv(pat, typ)
    else:
      result = nil
  of nnkPar:
    if containsForm(lang, lang.types[typ], pat[1][0].intVal.int):
      if countTags(lang, lang.types[typ]) == 1:
        result = pat # the type is only inhabited by the form
      else:
        result = makeConv(pat, typ)
    else:
      result = nil
  else:
    unreachable()

proc parsePattern(lang: LangInfo, n: NimNode): NimNode =
  ## Parses a pattern expression into its internal representation, assigning
  ## types in the process.
  case n.kind
  of nnkCall:
    if n[0].kind != nnkIdent:
      error("the head of a form pattern must be an identifier", n[0])

    # a form pattern may match multiple forms at the same time, with
    # potentially incompatible types (when wildcard patterns are used). Only
    # the embedder of the pattern has enough context to decide which ones to
    # cull, so all candidates are returned

    let matchAny = eqIdent(n[0], "_") or eqIdent(n[0], "any")

    # 1. parse and type all elements
    var hasListPattern = false
    var base = nnkCall.newTree(n[0])
    for i in 1..<n.len:
      let elem = parsePattern(lang, n[i])
      if elem[1].kind == nnkBracket:
        if hasListPattern:
          error("only a single '...' pattern is allowed per form", n[i])
        hasListPattern = true
      base.add elem

    result = nnkCurly.newTree()
    # 2. gather all forms fitting the pattern:
    for idx, it in lang.forms.pairs:
      if not matchAny and not eqIdent(n[0], it.name):
        continue

      var i = 0
      var prod = newCall(n[0])
      for ei in 1..<base.len:
        if i == it.elems.len:
          break

        let e = base[ei]
        let typ = e[1]
        case typ.kind
        of nnkEmpty, nnkNilLit, nnkIntLit, nnkPar, nnkCurly:
          # can receive all single items, but not lists
          if it.elems[i].repeat:
            break
          else:
            let got = fitTo(lang, it.elems[i].typ, e)
            if got.isNil:
              break
            else:
              prod.add got
              inc i
        of nnkBracket:
          var j = i
          let fin = it.elems.len - (base.len - ei) + 1
          var real = typ[0] ## inferred type
          case typ[0].kind
          of nnkEmpty:
            # special rule: a wildcard '...' pattern can match elements of
            # differing type
            j = fin
          of nnkNilLit:
            # inferred type. Pattern only matches sequences of elements of
            # the same type (no subtyping)
            while j < fin and it.elems[j].typ == it.elems[i].typ:
              inc j
            real = newIntLitNode(it.elems[i].typ)
          of nnkIntLit:
            while j < fin and it.elems[j].typ == typ[0].intVal:
              inc j
          else:
            unreachable()

          if j == i:
            break # a repetition must "consume" at least one source element
          i = j

          if real == typ[0]:
            prod.add e
          else:
            prod.add makeTyped(e[0], nnkBracket.newTree(real), typ)
        else:
          unreachable()

      if prod.len == n.len and i == it.elems.len:
        result.add makeTyped(prod, nnkPar.newTree(newIntLitNode(idx)), n)

    if result.len == 0:
      error("no form matches the given pattern", n)
    elif result.len == 1:
      result = result[0]
    else:
      result = makeTyped(result, nnkCurly.newTree(), n)
  of nnkBracket:
    if n.len != 1:
      error("invalid syntax", n)

    case n[0].kind
    of nnkIdent:
      let id = ident(parseVar(n[0]))
      # due to coalescing of match expressions, assigning an internal symbol
      # to the temporary binding is not yet possible
      let call = nnkInfix.newTree(ident"->", newEmptyNode(), quote do: dst.`id`)
      copyLineInfo(call, n)
      # the matched type needs to be inferred
      result = makeTyped(
        nnkTupleConstr.newTree(nnkExprEqExpr.newTree(n[0], call)),
        newNimNode(nnkNilLit), n)
    of nnkInfix:
      if n[0].len != 3 or not eqIdent(n[0][0], "->"):
        error("expected '->' infix call", n[0])
      let src = parseVar(n[0][1])
      if src notin lang.map:
        error(fmt"no meta-variable with name '{src}' exists", n[0][1])

      let id = ident(parseVar(n[0][2]))
      let call = nnkInfix.newTree(ident"->", n[0][1], quote do: dst.`id`)
      copyLineInfo(call, n)
      # bind the matched value to the first identifier and the result of
      # the application to the second identifier
      result = makeTyped(
        nnkTupleConstr.newTree(
          n[0][1],
          nnkExprEqExpr.newTree(n[0][2], call)),
        newIntLitNode(lang.map[src]), n)
    else:
      error("expected identifier or '->' infix call'", n[0])
  of nnkPrefix:
    if not n[0].eqIdent("..."):
      error("only `...` is allowed as a prefix", n[0])

    let tmp = parsePattern(lang, n[1])
    if tmp[1].kind notin {nnkIntLit, nnkEmpty, nnkNilLit}:
      error("only '...<meta-var>' and '...any' are allowed", n[1])
    # the '...' prefix is stripped from the expression
    result = makeTyped(tmp[0], nnkBracket.newTree(tmp[1]), n)
  of nnkIdent:
    if n.eqIdent("_"):
      # placeholder, type may be inferred
      result = makeTyped(n, newEmptyNode(), n)
    elif n.eqIdent("any"):
      # an alias for '_'
      result = makeTyped(ident"_", newEmptyNode(), n)
    else:
      # must be a meta-variable
      let typ = parseVar(n)
      if typ notin lang.map:
        error("no meta-variable with the give name exists", n)

      result = makeTyped(n, newIntLitNode(lang.map[typ]), n)
  else:
    error("syntax error", n)

proc patternToString(n: NimNode; indent = 0): string =
  case n.kind
  of nnkCurly:
    result = "{"
    result.add repr(n[0])
    for i in 1..<n.len:
      result.add "\n"
      for _ in 0..<indent+1:
        result.add "  "
      result.add patternToString(n[i], indent + 1)
    result.add "\n"
    for _ in 0..<indent:
      result.add "  "
    result.add "}"
  of nnkCall:
    result = repr(n[0])
    result.add "("
    for i in 1..<n.len-1:
      if i > 1:
        result.add ", "
      result.add repr(n[i])
    if n.len > 2:
      result.add ", "
    result.add patternToString(n[^1], indent)
    result.add ")"
  of nnkPar:
    result = "^"
    result.add repr(n[0])
    result.add " "
    result.add patternToString(n[1], indent)
  of nnkEmpty:
    result = "."
  of nnkStmtList:
    result = "<cont>"
  of nnkTupleConstr:
    result = "("
    result.add repr(n[0])
    result.add ", <cont>)"
  else:
    result = "<error:" & $n.kind & ">"

proc generateForMatch(lang: LangInfo, name, ast, sel, e, els: NimNode,
                      config: ExpandConfig): NimNode =
  ## Generates the NimSkull code for a match expression `expr`. `els` is either
  ## an `nnkElse` tree used for handling the rest of match, or nil, in which
  ## case how to handle the rest of a match is dictated by `config`.
  let cursor = genSym("cursor")
  let backup = genSym("backup")

  var stack: seq[tuple[len, saved: NimNode]] ## cursor context stack
  var top: NimNode
    ## the topmost non-union match expression enclosing the currently
    ## processed one
  var hasUsedElse = false

  proc aux(lang: LangInfo, e, to: NimNode): NimNode =
    ## Does the actual work.
    proc tm(lang: LangInfo, e, to: NimNode): NimNode =
      if e[1].kind != nnkEmpty:
        # commit the current cursor to a local with the given name
        if e[0].kind == nnkBracket:
          let bias = e[2]
          let len = stack[^1].len # can only be non-empty
          to.add newLetStmt(e[1], quote do: (`cursor`, `len` - `bias`))
        else:
          to.add newLetStmt(e[1], quote do: get(`ast`, `cursor`))

      # only emit a cursor movement when the moved cursor is actually observed
      if e[^1].kind in {nnkCall, nnkCurly, nnkPar}:
        case e[0].kind
        of nnkPar:
          let nlen = genSym"len"
          let saved = genSym"saved"
          to.add quote do:
            let `nlen` = `ast`[pos(`cursor`)].val
            let `saved` = enter(`ast`, `cursor`)

          stack.add (nlen, saved)
        of nnkEmpty, nnkIntLit:
          to.add quote do:
            advance(`ast`, `cursor`)
        of nnkBracket:
          let bias = e[2]
          let len = stack[^1].len # can only be non-empty
          to.add quote do:
            for _ in 0 ..< (`len` - `bias`):
              advance(`ast`, `cursor`)
        else:
          unreachable(e[0].kind)

      result = aux(lang, e[^1], to)

    case e.kind
    of nnkCall:
      result = tm(lang, e, to)
    of nnkPar:
      # move the current cursor to the end of the subtree and pop it from
      # the stack
      let (_, saved) = stack.pop()
      to.add quote do:
        restore(`ast`, `cursor`, `saved`)
      result = aux(lang, e[0], to)
    of nnkCurly:
      # a dispatcher
      proc genOfBranch(lang: LangInfo, typ: LangType, used: var IntSet,
                       allowEmpty=true): NimNode =
        result = nnkOfBranch.newTree()
        case typ.kind
        of tkTerminal:
          if not containsOrIncl(used, typ.ntag) or not allowEmpty:
            result.add newIntLitNode(typ.ntag)
        of tkRecord:
          if not containsOrIncl(used, typ.rtag) or not allowEmpty:
            result.add newIntLitNode(typ.rtag)
        of tkNonTerminal:
          let ntags = ntags(lang, typ)
          for tag in ntags(lang, typ):
            if not containsOrIncl(used, tag):
              result.add newIntLitNode(tag)

          if not allowEmpty and result.len == 0:
            # any node tag part of the non-terminal would do
            result.add newIntLitNode(ntags[0])

      let stackLen = stack.len
      let typ = e[0].intVal.int
      var caseStmt = nnkCaseStmt.newTree(quote do: `ast`[pos(`cursor`)].kind)
      var used = initIntSet()
      for i in 1..<e.len:
        let it = e[i]
        var handler: NimNode
        case it[0].kind
        of nnkPar:
          handler = nnkOfBranch.newTree()
          for x in it[0].items:
            handler.add newIntLitNode(lang.forms[x.intVal].ntag)
            used.incl(lang.forms[x.intVal].ntag)
        of nnkEmpty:
          # matches the rest
          handler = genOfBranch(lang, lang.types[typ], used)

          if handler.len == 0:
            # turn into an else branch, but also add an extra else branch
            # before it, so that the compiler emits a helpful warning about
            # the branch being unreachable
            caseStmt.add nnkElse.newTree(newCall(bindSym"unreachable"))
            handler = nnkElse.newTree()
        of nnkIntLit:
          # always add a branch, even if the tag already appeared. The
          # NimSkull compiler will report an error for the duplicate label
          handler = genOfBranch(lang, lang.types[it[0].intVal], used, false)
        of nnkBracket:
          handler = genOfBranch(lang, lang.types[it[0][0].intVal], used, false)
        else:
          unreachable()

        if stack.len == 0:
          top = it

        handler.add newStmtList()
        discard tm(lang, it, handler[^1])
        caseStmt.add handler
        # pop all leftover len entries
        stack.setLen(stackLen)

      let info = e[0]
      # handle the uncovered values, if any
      if els != nil:
        let b = genOfBranch(lang, lang.types[typ], used)
        if b.len > 0: # are there any uncovered values?
          caseStmt.add els
          hasUsedElse = true

        if stack.len == 0 and not hasUsedElse:
          # the 'else' rule was never used. Add it to the top-level case
          # statement such that a warning will be emitted
          if caseStmt[^1].kind != nnkElse:
            caseStmt.add nnkElse.newTree(newCall(bindSym"unreachable"))
          caseStmt.add els
      elif stack.len > 0 and config.fillForm != nil:
        # uncovered values in nested positions are handled by processing
        # the whole production
        assert top.kind == nnkCall and top[0].kind == nnkPar
        var allCovered = true
        for tag in ntags(lang, lang.types[typ]):
          if tag notin used:
            allCovered = false
            break

        # important: the `backup` cursor has to be used here, as it still
        # points to the original node, whereas `cursor` has been moved already
        if allCovered:
          discard "nothing to do"
        elif top[0].len == 1:
          # simple case. The form ID is known statically
          caseStmt.add nnkElse.newTree(
            config.fillForm(lang, top[0][0].intVal.int, backup, info))
        else:
          # complex case. The form ID is only known at run-time; dispatch over
          # the entry-level node's kind for detecting the form
          let inner = nnkCaseStmt.newTree(
            quote do: `ast`.nodes[pos(`backup`)].kind)
          for it in top[0].items:
            inner.add nnkOfBranch.newTree(it,
              config.fillForm(lang, it.intVal.int, backup, info))
          inner.add nnkElse.newTree(newCall(bindSym"unreachable"))
          caseStmt.add nnkElse.newTree(inner)
      else:
        var
          fillForm = config.fillForm
          fillType = config.fillType

        # always report an error for nested productions when form-filling
        # is unavailable
        if fillForm.isNil or stack.len > 0:
          fillForm = defaultFillForm
        if fillType.isNil or stack.len > 0:
          fillType = defaultFillType

        for it in lang.types[typ].forms.items:
          if lang.forms[it].ntag notin used:
            caseStmt.add nnkOfBranch.newTree(
              newIntLitNode(lang.forms[it].ntag),
              fillForm(lang, it, cursor, info))

        # fill in handling for not fully handled subtypes
        for it in lang.types[typ].sub.items:
          let br = genOfBranch(lang, lang.types[it], used)
          if br.len > 0:
            br.add fillType(lang, it, cursor, info)
            caseStmt.add br

      if caseStmt[^1].kind != nnkElse:
        # all allowed node tags are handled, the rest are known to
        # be impossible
        caseStmt.add nnkElse.newTree(newCall(bindSym"unreachable"))

      to.add caseStmt
      # nothing may follow a dispatcher
      result = nil
    of nnkTupleConstr:
      # in-place transform the identdefs into proper ones

      proc transformSource(lang: LangInfo, pos, typ, orig: NimNode): NimNode =
        case typ.kind
        of nnkIntLit:
          # a single item binding
          let mvar = ident(lang.types[typ.intVal].mvar)
          if pos.kind == nnkIdent:
            pos # the source is a bound identifier already
          else:
            case lang.types[typ.intVal].kind
            of tkTerminal:
              quote do: `name`.`mvar`(index: `ast`[`pos`].val)
            of tkRecord:
              quote do: `name`.`mvar`(id: `ast`[`pos`].val)
            of tkNonTerminal:
              quote do: `name`.`mvar`(index: `pos`)
        of nnkBracket:
          # a list binding
          let mvar = ident(lang.types[typ[0].intVal].mvar)
          if pos.kind == nnkIdent:
            pos # the source is already a slice (bound to an identifier)
          else:
            quote do:
              slice[`name`.`mvar`](addr `ast`, `pos`[0], uint32(`pos`[1]))
        else:
          unreachable()

      for it in e[0].items:
        case it[2].kind
        of nnkSym:
          it[2] = transformSource(lang, it[2], it[1], it[2])
        else:
          it[2][1] = transformSource(lang, it[2][1], it[1], it[2])
        it[1] = newEmptyNode()

      to.add e[0]
      to.add e[1]
      result = nil
    of nnkStmtList:
      to.add e
      result = nil # statement lists are always trailing
    else:
      unreachable(e.kind)

  result = nnkStmtList.newTree()
  result.add newVarStmt(cursor, sel)
  result.add newVarStmt(backup, cursor)
  discard aux(lang, e, result)

proc patternToMatch(n: NimNode): tuple[head, tail: NimNode] =
  ## Translates a pattern into a match expression. A match expression has the
  ## following structure:
  ##
  ## match ::= (nkCall (nkBracket <typ>) <name> <int> <cont>)
  ##        |  (nkCall (nkPar <int>+) <name> <cont>)
  ##        |  (nkCall <typ> <name> <cont>)
  ## name  ::= <int> | <empty>
  ## cont  ::= <match>
  ##        |  (nkPar <cont>)                         # leave sub match
  ##        |  (nkCurly <int> <match>+)               # union matching
  ##        |  (nkTupleConstr (nkLetSection ...) ...) # binding
  ##        |  (nkStmtList ...)                       # custom tail logic
  var binds: NimNode
  proc addBinding(got: NimNode) =
    if binds.isNil:
      binds = nnkLetSection.newTree()
    binds.add got

  let empty = newEmptyNode() # save some allocations

  proc aux(n: NimNode, depth: int): tuple[head, tail: NimNode, depth: int] =
    let e = n[0]
    let typ = n[1]
    case typ.kind
    of nnkPar:
      result.head = nnkCall.newTree(typ, empty)
      result.tail = result.head
      assert e.kind == nnkCall
      var depth = depth + 1
      for i in 1..<e.len:
        let (head, tail, d) = aux(e[i], depth)
        result.tail.add head
        result.tail = tail
        depth = d
        if e[i][1].kind == nnkBracket:
          # append the length bias to the list matcher
          result.tail.add newIntLitNode(e.len - 2)
      result.tail.add newTree(nnkPar)
      result.tail = result.tail[^1]
      result.depth = depth
    of nnkBracket:
      result.head = nnkCall.newTree(typ, empty)
      # the bias is computed and attached by the enclosing processing
      result.tail = result.head
      result.depth = depth + 1
    of nnkEmpty:
      result.head = nnkCall.newTree(typ, empty)
      result.tail = result.head
      result.depth = depth + 1
    of nnkIntLit:
      if e.kind == nnkConv:
        # turn into a union deconstruction
        result = aux(e[0], depth)
        result.head = nnkCurly.newTree(typ, result.head)
      else:
        result.head = nnkCall.newTree(typ, empty)
        result.tail = result.head
        result.depth = depth + 1
    else:
      unreachable(typ.kind)

    # extract the bindings:
    case e.kind
    of nnkIdent:
      if not eqIdent(e, "_"):
        addBinding(newIdentDefs(e, typ, newIntLitNode(depth)))
    of nnkTupleConstr:
      for it in e.items:
        if it.kind == nnkIdent:
          addBinding(newIdentDefs(it, typ, newIntLitNode(depth)))
        else:
          if it[1][1].kind == nnkEmpty:
            it[1][1] = newIntLitNode(depth)
          addBinding(newIdentDefs(it[0], typ, it[1]))
    else:
      discard "not something with any bindings"

  (result.head, result.tail) = aux(n, 0)
  if binds != nil:
    result.tail.add nnkTupleConstr.newTree(binds)
    result.tail = result.tail[^1]

proc mergeInto(a, b: NimNode): NimNode =
  ## Merges the match expression `a` into the match expression `b`, using a
  ## simple top-down zip-like algorithm.
  proc canMerge(a, b: NimNode): bool =
    if a[0] == b[0] and a[0].kind != nnkBracket: # same head?
      true
    else:
      false

  case b.kind
  of nnkCurly:
    # merge the source matchers into the target matchers
    if a.kind == nnkCall:
      # `a` is a matcher tha covers the full set of values for the type; just
      # append it at the end
      b.add a
    else:
      assert a.kind == nnkCurly
      for i in 1..<a.len:
        block search:
          for j in 1..<b.len:
            if canMerge(a[i], b[^1]):
              b[^1] = mergeInto(a[i], b[^1])
              break search
          # cannot merge into any existing matcher
          b.add a[i]
    b
  of nnkNilLit:
    a
  of nnkCall:
    # can only mean that the heads are the same
    b[^1] = mergeInto(a[^1], b[^1])
    b
  else:
    unreachable()

proc assignSymbols(n: NimNode) =
  ## Turns the relative addressing for bindings into absolute addressing by
  ## giving a name (i.e., gensym) to every match expression whose result is
  ## used in a binding.
  var map: Table[int, NimNode] ## depth -> list of identDefs
  proc step(n: NimNode, depth: int) =
    case n.kind
    of nnkCall:
      step(n[^1], depth + 1)
      var defs: NimNode
      if pop(map, depth, defs):
        let s = genSym"pos"
        n[1] = s
        for it in defs.items:
          if it[^1].kind in nnkCallKinds:
            it[^1][1] = s
          else:
            it[^1] = s
    of nnkCurly:
      for i in 1..<n.len:
        step(n[i], depth)
    of nnkPar:
      step(n[^1], depth)
    of nnkTupleConstr:
      # add the identDefs of all bindings referencing match expression results
      # to the table
      for it in n[0].items:
        let id =
          if it[^1].kind == nnkIntLit:
            it[^1].intVal.int
          elif it[^1][1].kind == nnkIntLit:
            it[^1][1].intVal.int
          else:
            continue
        if id in map:
          map[id].add it
        else:
          map[id] = nnkBracket.newTree(it)
    of nnkStmtList:
      discard "nothing to do"
    else:
      unreachable(n.kind)

  step(n, 0)

proc optimize(n: NimNode; trailing=true): NimNode =
  ## Elides all match expressions of which the result and side-effects are
  ## not used.
  const Terminators = {nnkStmtList, nnkTupleConstr}
  case n.kind
  of nnkCurly:
    result = n
    for i in 1..<n.len:
      result[i] = optimize(n[i], false)
  of nnkCall:
    let last = optimize(n[^1])
    if trailing and n[1].kind == nnkEmpty and last.kind in Terminators:
      result = last
    else:
      result = n
      result[^1] = last
  of nnkPar:
    let last = optimize(n[^1])
    if trailing and last.kind in Terminators:
      result = last
    else:
      result = n
      result[^1] = last
  of Terminators:
    result = n
  else:
    unreachable(n.kind)

proc matchImpl*(lang: LangInfo, src: int, name, ast, sel, rules: NimNode,
                config: ExpandConfig): NimNode =
  ## The heart of the `match` macro, combining the various parsing, typing,
  ## validation, and translation. `src` is the ID of the type of the to-be-
  ## matched non-terminal, `name` is a type expression referring to the
  ## language the non-terminal is part of.
  var total = NimNode(nil)
  var els   = NimNode(nil)
  for it in rules.items:
    case it.kind
    of nnkOfBranch:
      it.expectLen 2
      if els != nil:
        error("'else' rule must appear last", els)

      var pat = parsePattern(lang, it[0])
      if pat.kind == nnkExprColonExpr and pat[1].kind == nnkBracket:
        error("a repetition pattern is not allowed at the top-level", it[0])

      pat = fitTo(lang, src, pat)
      if pat.isNil:
        error("pattern doesn't match any production of non-terminal", it[0])

      let (head, tail) = patternToMatch(pat)
      # set the body as the continuation for the innermost matcher
      if it[1].kind == nnkStmtList:
        tail.add it[1]
      else:
        tail.add newStmtList(it[1])

      total = mergeInto(head, total)
    of nnkElse:
      # 'else' is special, in that it terminates all matchers, not just the top-
      # level one. Ideally, this would not require duplicating the body of the
      # 'else' branch, but the other approaches either mess with the body's
      # semantics (procedure wrapping: might need captures, interferes with
      # ``return`` and ``break``) or cannot handle both expressions and
      # statements at the same time (with a blocks-and-break approach)
      if els.isNil:
        els = it
      else:
        error("only a single 'else' rule is allowed", it)
    else:
      error("expected 'of' or 'else'", it)

  if total.isNil:
    # happens when there are no rules (with is allowed)
    total = nnkCurly.newTree(newIntLitNode(src))

  assignSymbols(total)
  result = generateForMatch(lang, name, ast, sel, optimize(total), els, config)

macro matchImpl(lang: static LangInfo, nterm: static string,
                name: typed, ast: Tree, cursor: untyped,
                info: untyped, rules: varargs[untyped]): untyped =
  ## The internal implementation `match` dispatches to.
  # report an error for all missing form and type handling
  let config = ExpandConfig(
    fillForm: nil,
    fillType: nil
  )

  copyLineInfo(cursor, info) # for better source locations
  result = matchImpl(lang, lang.map[nterm], name, ast, cursor, rules, config)

template match*[L; N: static](ast: Tree, cursor, info: untyped,
                              branches: varargs[untyped]): untyped =
  ## Type-unsafe version of ``match``, meant for internal usage.
  bind matchImpl
  matchImpl(idef(typeof(L)), N, typeof(L), ast, cursor, info, branches)

template match*[L, N](ast: Ast[L, auto], nt: Metavar[L, N],
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
  matchImpl(idef(typeof(L)), N, L, ast.tree, Cursor(nt.index), nt, branches)
