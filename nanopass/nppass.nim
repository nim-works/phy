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
      build(`to`, `ret`, body)

  result = def

macro processorMatchImpl(lang: static LangInfo, src: static string,
                         sel: untyped, rules: varargs[untyped]): untyped =
  ## Implements the transformation/expansion of a language->language
  ## processor's trailing case statement/expression.
  let id = lang.map[src]
  var (branches, used) = matchImpl(lang, id, ident"in.ast", sel, rules)

  template nt: untyped = lang.types[id]
  let sym = bindSym"transform"
  # auto-generate the transformers for the forms not manually provided:
  for it in nt.forms.items:
    let id = lang.forms[it].ntag
    if not containsOrIncl(used, id):
      branches.add nnkOfBranch.newTree(
        newIntLitNode(id),
        (quote do:
          (typeof(result))(
            index: `sym`(idef(src), idef(dst), typeof(result).N, `it`, `sel`))))

  # auto-generate the branches for missing production terminals and
  # non-terminals:
  for it in nt.sub.items:
    if lang.types[it].terminal:
      let id = lang.types[it].ntag
      if id notin used:
        let to = ident"out.ast"
        let input = ident"in.ast"
        branches.add nnkOfBranch.newTree(
          newIntLitNode(id),
          (quote do:
            # TODO: use the tag of the destination language
            `to`.nodes.add:
              TreeNode[uint8](kind: uint8(`id`), val: `input`[`sel`].val)
            (typeof(result))(index: NodeIndex(`to`.nodes.high))))
    else:
      # if the first form's tag is used, so is the non-terminal itself
      if lang.forms[lang.types[it].forms[0]].ntag notin used:
        # TODO: consider inlining the transformer if it's auto-generated.
        #       More code to emit, but also a little less work at run-time
        let branch = nnkOfBranch.newTree()
        for tag in ntags(lang, lang.types[it]).items:
          branch.add newIntLitNode(tag)
        let name = ident(lang.types[it].mvar)
        let callee = ident"->"
        # dispatch to the processor and convert to the expected type
        branch.add quote do:
          (typeof(result))(
            index: `callee`(src.`name`(index: `sel`), dst.`name`).index)
        branches.add branch

  let input = ident"in.ast"
  result = nnkCaseStmt.newTree(quote do: `input`[`sel`].kind)
  result.add branches
  if branches[^1].kind != nnkElse:
    # the selector is a uint8 and thus the case cannot be exhaustive
    result.add nnkElse.newTree(newCall(ident"unreachable"))

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
    `sym`(idef(src), `nterm`, `index`)

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
      processorMatchImpl(idef(src), typeof(arg).N, arg.index)
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
      build(`to`, `ret`, body)

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
  let storage = ident"io.storage"
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
    let inj = ident"[]"
    body.add quote do:
      template match(sel: Metavar, branches: varargs[untyped]): untyped {.used.} =
        match(`input`, sel, branches)

      template `inj`(x: ChildSlice, i: SomeInteger): untyped {.used.} =
        `input`[x, i]

      template val[T](v: nanopass.Value[T]): T {.used.} =
        # TODO: return a `lent T` where ``unpack`` does too (this is tricky...)
        # XXX: consider renaming this template to `get`
        unpack(`storage`[], v.index, typeof(T))

  if hasOut:
    let embed = bindSym"embed"
    body.add quote do:
      template terminal(x: untyped): untyped {.used.} =
        `embed`(`storage`, x)
      template build(n: typedesc[Metavar], body: untyped): untyped {.used.} =
        build(`output`, n, body)

  if hasIn:
    # re-use the data storage object from the input
    body.add quote do:
      let `storage` = `input`.storage
  else:
    body.add quote do:
      let `storage` = new(`storageTy`)

  if hasIn:
    # shadow the input tree with a cursor to prevent a costly copy when
    # it's captured by the closure
    body.add quote do:
      let `input` {.cursor.} = `input`.tree
  if hasOut:
    body.add quote do:
      var `output`: Ast[dst, `storageTy`].tree
      let index = `call`.index
      # turn the AST with indirections into one without
      result = Ast[dst, `storageTy`](
        tree: finish(`output`, index),
        storage: `storage`,
      )
  else:
    body.add quote do:
      result = `call`

  def.body = body
  # patch the signature:
  if hasIn:
    def.params[1][^2] = bindSym"NodeIndex"
    def.params.insert(1, newIdentDefs(input, quote do: Ast[`src`, `storageTy`]))
  if hasOut:
    def.params[0] = nnkBracketExpr.newTree(ident"Ast", dst, storageTy)

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

  # if the body doesn't end in an expression, add a call to the
  # entry processor
  if def.body[^1].kind == nnkProcDef:
    # ^^ a heuristic, but should work okay enough
    def.body.add newCall(ident"->", def.params[1][0],
      newDotExpr(newDotExpr(dst, ident"meta"), ident"entry"))

  def.body = newStmtList(preamble, def.body)

  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)
  lambda.params[0] = dstnterm
  lambda.params[1][^2] = srcnterm

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  call[1] = nnkObjConstr.newTree(srcnterm,
    nnkExprColonExpr.newTree(ident"index", call[1]))
  result = assemblePass(src, dst, def, call)

macro inpassImpl(name, nterm: typedesc, def: untyped) =
  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)
  lambda.params[0] = nterm

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  result = assemblePass(nil, name, def, call)

macro outpassImpl(name, nterm: typedesc, def: untyped) =
  let lambda = newProc(newEmptyNode(), body=def.body, procType=nnkProcDef)
  lambda.params = copyNimTree(def.params)
  lambda.params[1][^2] = nterm

  let call = newCall(lambda)
  # forward the original parameters to the lambda:
  for i in 1..<def.params.len:
    for j in 0..<def.params[i].len-2:
      call.add def.params[i][j]

  call[1] = nnkObjConstr.newTree(nterm,
    nnkExprColonExpr.newTree(ident"index", call[1]))
  result = assemblePass(name, nil, def, call)

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
    when typ is Metavar:
      inpassImpl(typ.L, typ, p)
    else:
      # use the entry non-terminal
      inpassImpl(typ, typ.meta.entry, p)

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
    when target is Metavar:
      passImpl(input, target.L, input, target, p)
    else:
      # use the entry non-terminal
      passImpl(input, target, input.meta.entry, target.meta.entry, p)

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

  result = genAst(typ = p.params[1][^2], p):
    when typ is Metavar:
      outpassImpl(typ.L, typ, p)
    else:
      # use the entry non-terminal
      outpassImpl(typ, typ.meta.entry, p)
