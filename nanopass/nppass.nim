## Implements the various pass macros.

import std/[genasts, macros, packedsets, tables]
import nanopass/[asts, nplang, nplangdef, npmatch, nptransform]

template embed(storage, arg: untyped): untyped =
  ## Implements terminal value construction.
  mixin pack
  let tmp = arg
  Value[typeof(tmp)](index: pack(storage[], tmp))

macro transformOutImpl(lang: static LangDef, name, def: untyped) =
  ## Implements the transformation for processors in an *->language pass.
  if def.kind notin {nnkProcDef, nnkFuncDef}:
    error(".transform must be applied to procedure definition", def)

  if def.body.kind == nnkEmpty:
    # a forward declaration, bail
    return def

  let to = ident"out.ast"
  let ret = def.params[0]
  def.body = newStmtList(def.body)
  def.body.insert 0, quote do:
    # inject a build overload that implicitly uses the output language
    template build(body: untyped): untyped {.used.} =
      build(`to`.tree, `ret`, body)

  result = def

macro processorMatchImpl(lang: static LangInfo, src: static string,
                         sel: untyped, rules: varargs[untyped]): untyped =
  ## Implements the transformation/expansion of a language->language
  ## processor's trailing case statement/expression.
  let input  = newDotExpr(ident"in.ast", ident"tree")
  let output = newDotExpr(ident"out.ast", ident"tree")

  proc fillForm(lang: LangInfo, form: int, n, info: NimNode): NimNode =
    ## Generates a form transformer.
    let sym = bindSym"transform"
    result = quote do:
      (typeof(result))(
        index: `sym`(idef(src), idef(dst), typeof(result).N, `form`,
                     `input`, `output`, `n`))
    copyLineInfo(result[1][1][^1], info)

  proc fillType(lang: LangInfo, typ: int, n, info: NimNode): NimNode =
    ## Generates a call to the type transformer for `typ`.
    let sym = bindSym"transformType"
    result = quote do:
      (typeof(result))(
        index: `sym`(idef(src), idef(dst), typeof(result).N, `typ`,
                     `input`, `output`, `n`))
    copyLineInfo(result[1][1][^1], info)

  let config = ExpandConfig(
    fillForm: fillForm,
    fillType: fillType,
  )

  matchImpl(lang, lang.map[src], ident"src", input, sel, rules, config)

macro genProcessor*(index, nterm: untyped): untyped =
  ## Generates the body for a non-terminal processor.
  # simply emit an empty processorMatchImpl invocation. All branches will be
  # auto-generated
  # TODO: if none of the productions require a (direct or indirect) call to a
  #       custom processor, the source and target productions match, and the
  #       used tags map to the same ID in the source and target language, use a
  #       memcopy
  let sym = bindSym"processorMatchImpl"
  result = quote do:
    `sym`(idef(src), `nterm`, Cursor(`index`))

proc hasPragma(def: NimNode, name: string): bool =
  if def.pragma.kind == nnkPragma:
    for it in def.pragma.items:
      if it.eqIdent(name):
        return true

macro genAdapter[T1, T2; A, B: static string](
    src: typedesc[Metavar[T1, A]], dst: typedesc[Metavar[T2, B]],
    orig: untyped) =
  # note: the macro signature is very specific because it acts as the type
  # checking for programmer-provided processor signatures
  let name = ident("->")
  copyLineInfo(name, orig)
  result = quote do:
    template `name`(n: `src`, _: typedesc[`dst`]): `dst` =
      {.line.}: `orig`(n)

macro transformInOutImpl(lang: static LangDef, name, def: untyped) =
  ## Implements the transformation for language->language pass processors.
  let name = name
  if def.kind notin {nnkProcDef, nnkFuncDef}:
    error(".transform must be applied to procedure definition", def)

  if def.params[0].kind == nnkEmpty:
    error("a return type is required for a transfomer", def.name)

  if def.body.kind == nnkEmpty:
    # a forward declaration. Append the additional adapter procedure
    return newStmtList(def,
      newCall(bindSym"genAdapter",
        copyNimTree(def.params[1][^2]),
        copyNimTree(def.params[0]),
        copyNimNode(def.name)))

  proc transformCase(n: NimNode): NimNode =
    result = genAst(arg=n[0]):
      processorMatchImpl(idef(src), typeof(arg).N, Cursor(arg.index))
    copyLineInfo(result, n)
    for i in 1..<n.len:
      result.add n[i]

  var inner = def.body
  if inner.kind == nnkCaseStmt:
    inner = transformCase(inner)
  elif inner.kind == nnkStmtList:
    if inner[^1].kind == nnkCaseStmt:
      inner[^1] = transformCase(inner[^1])
    else:
      error("trailing statement/expression must be 'case'", inner[^1])
  else:
    error("trailing statement/expression must be 'case'", inner)

  let to = ident"out.ast"
  let ret = def.params[0]
  def.body = newStmtList(def.body)
  def.body.insert 0, quote do:
    # inject a build macro overload that implicitly uses the
    # target non-terminal
    template build(body: untyped): untyped {.used.} =
      build(`to`.tree, `ret`, body)

  result = def

macro transformInImpl(lang: static LangDef, name, def: untyped) =
  ## Implements the processing for transformers part of an input pass.
  result = def

macro generatedImpl(def: untyped) =
  ## Implements the `.generated` pragma for language->language passes.
  if def.body.kind != nnkEmpty:
    error(".generated must be applied to forward declaration", def)

  def.body = newCall(ident"->", def.params[1][0], copyNimTree(def.params[0]))
  result = def

proc assemblePass(src, dst, def, call: NimNode): NimNode =
  ## Assembles the final procedure definition for a pass. `def` is the original
  ## proc definition, `call` the call to the pass' implementation.
  let input = ident"in.ast"
  let output = ident"out.ast"
  let storageTy = ident"Literals" # TODO: don't hardcode
  let hasIn = src != nil
  let hasOut = dst != nil

  var body = newStmtList()
  let (transformImpl, name) =
    if hasIn and hasOut:
      (bindSym"transformInOutImpl", dst)
    elif hasIn:
      (bindSym"transformInImpl", src)
    elif hasOut:
      (bindSym"transformOutImpl", dst)
    else:
      unreachable()

  body.add quote do:
    template transform(p: untyped) {.used.} =
      `transformImpl`(def(`name`), `name`, p)

  if hasIn and hasOut:
    let impl = bindSym"generatedImpl"
    body.add quote do:
      template generated(p: untyped) {.used.} = `impl`(p)

  # alias the source and destination language with known names:
  if hasIn:
    body.add quote do:
      template src: untyped {.used.} = `src`
  if hasOut:
    body.add quote do:
      template dst: untyped {.used.} = `dst`

  if hasIn:
    body.add quote do:
      template match[N](sel: Metavar[src, N], branches: varargs[untyped]): untyped {.used.} =
        match[src, N](`input`.tree, Cursor(sel.index), sel, branches)

      template slice[N](T: typedesc[Metavar[src, N]]): typedesc {.used.} =
        ChildSlice[T, Cursor]
      template slice(T: typedesc[asts.Value[auto]]): typedesc {.used.} =
        ChildSlice[T, Cursor]

      template val[T](v: nanopass.Value[T]): T {.used.} =
        # TODO: return a `lent T` where ``unpack`` does too (this is tricky...)
        # XXX: consider renaming this template to `get`
        unpack(`input`.storage[], v.index, typeof(T))

      template equal[N](a, b: Metavar[src, N]): bool {.used.} =
        equal(`input`.tree, Cursor(a.index), Cursor(b.index))

  if hasOut:
    let embed = bindSym"embed"
    body.add quote do:
      template terminal(x: untyped): untyped {.used.} =
        `embed`(`output`.storage, x)
      template build(n: typedesc[Metavar], body: untyped): untyped {.used.} =
        build(`output`.tree, n, body)
      template match[N](sel: Metavar[dst, N], branches: varargs[untyped]): untyped {.used.} =
        match[dst, N](`output`.tree, IndCursor(sel.index), sel, branches)
      template slice[N](T: typedesc[Metavar[dst, N]]): typedesc {.used.} =
        ChildSlice[T, IndCursor]

      template equal[N](a, b: Metavar[dst, N]): bool {.used.} =
        equal(`output`.tree, IndCursor(a.index), IndCursor(b.index))

  if hasIn:
    # shadow the input tree with a cursor to prevent a costly copy when
    # it's captured by the closure
    body.add quote do:
      let `input` {.cursor.} = `input`
  if hasOut:
    body.add quote do:
      var `output` = Ast[dst, `storageTy`]()
    if hasIn:
      # re-use the storage from the input
      body.add quote do:
        `output`.storage = `input`.storage
    else:
      body.add quote do:
        `output`.storage = new(`storageTy`)
    body.add quote do:
      let pos = `call`
      # turn the AST with indirections into one without
      `output`.tree = finish(`output`.tree, pos.index)
      result = (move `output`, typeof(pos)(index: NodeIndex(0)))
  else:
    body.add quote do:
      result = `call`

  def.body = body
  # patch the signature:
  if hasIn:
    def.params.insert(1,
      newIdentDefs(input,
        nnkBracketExpr.newTree(ident"Ast", src, storageTy)))
  if hasOut:
    def.params[0] =
      nnkTupleConstr.newTree(
        nnkBracketExpr.newTree(ident"Ast", dst, storageTy),
        def.params[0])

  result = def

macro passImpl(src, dst, srcnterm, dstnterm: typedesc, def: untyped) =
  # create a forward declaration for each transformer:
  var preamble = newStmtList()
  var i = 0
  while i < def.body.len:
    let it = def.body[i]
    # not ideal, as it breaks some custom macro/template pragmas, but without
    # resorting to typed macros, there's no other way to do this transform
    if it.kind == nnkProcDef and it.hasPragma("transform"):
      if it.body.kind == nnkEmpty:
        # remove the user-defined forward declaration
        def.body.del(i)
        dec i # undo the following `inc`
      else:
        let backup = it.body
        it.body = newEmptyNode()
        preamble.add copyNimTree(it)
        it.body = backup
    inc i

  # add the generic processor procedure, which all processor invocations
  # for processors not supplied by the programmer will end up using
  let name = ident"->"
  preamble.add quote do:
    # note: the signature is overly broad, so that overload resolution
    # prefers the more specific adapters created for the programmer-provided
    # processors
    proc `name`[U, X](n: U, T: typedesc[Metavar[`dst`, X]]): T =
      genProcessor(n.index, U.N)

    proc `name`[T, C, N](s: ChildSlice[T, C],
                         U: typedesc[Metavar[`dst`, N]]): seq[U] {.closure.} =
      # XXX: the explicit .closure annotation works around a closure inference
      #      compiler bug
      result = newSeq[U](s.len)
      for i, it in s.pairs:
        result[i] = `name`(it, U)

  # if the body doesn't end in an expression, add a call to the
  # entry processor
  if def.body[^1].kind == nnkProcDef:
    # ^^ a heuristic, but should work okay enough
    def.body.add newCall(ident"->", def.params[1][0], dstnterm)

  def.body = newStmtList(preamble, def.body)
  def.params[0] = dstnterm
  def.params[1][^2] = srcnterm

  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  result = assemblePass(src, dst, def, call)

macro inpassImpl(name, nterm: typedesc, def: untyped) =
  def.params[0] = nterm

  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  result = assemblePass(nil, name, def, call)

macro outpassImpl(name, nterm: typedesc, def: untyped) =
  def.params[1][^2] = nterm

  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  result = assemblePass(name, nil, def, call)

template nterm(x: typedesc[Metavar]): typedesc = x
template nterm(x: typedesc): typedesc          = x.meta.entry

template lang(x: typedesc[Metavar]): typedesc = x.L
template lang(x: typedesc): typedesc          = x

macro inpass*(p: untyped) =
  ## Turns a procedure definition into a pass that takes arbitrary data as
  ## input and produces an AST for the specified language.
  ## The procedure's return type specifies the shape of the returned AST and
  ## must must be the non-terminal of an IL. As a short-hand, just specifying
  ## an IL is equivalent to specifying the IL's entry non-terminal.
  ##
  ## The return type of the transformed procedure is an AST.
  if p.kind != nnkProcDef:
    error(".inpass must be applied to a procedure definition", p)

  var typ = p.params[0]
  if typ.kind == nnkEmpty:
    error("a return type is required, but none is provided", p.params[0])

  result = genAst(typ, p):
    inpassImpl(lang(typ), nterm(typ), p)

macro pass*(p: untyped) =
  ## Turns a procedure definition into a language->language pass, that is a
  ## pass, that takes an AST (fragment) of language A and produces an AST of
  ## language B.
  if p.kind != nnkProcDef:
    error(".inpass must be applied to a procedure definition", p)

  var target = p.params[0]
  if target.kind == nnkEmpty:
    error("a return type is required, but none is provided", p.params[0])
  if p.params.len == 1:
    error("the input parameter is missing", p.params)

  result = genAst(input = p.params[1][^2], target, p):
    passImpl(lang(input), lang(target), nterm(input), nterm(target), p)

macro outpass*(p: untyped) =
  ## Turns a procedure definition into a language->* pass, that is, a pass
  ## that takes an AST (fragment) of language A and produces a value.
  if p.kind != nnkProcDef:
    error(".outpass must be applied to a procedure definition", p)

  let ret = p.params[0]
  if ret.kind == nnkEmpty:
    error("a return type is required, but none is provided", ret)
  if p.params.len == 1:
    error("the input parameter is missing", p.params)

  result = genAst(input = p.params[1][^2], p):
    outpassImpl(lang(input), nterm(input), p)
