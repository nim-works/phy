## Temporary test orchestrator that runs all tests in the ``expr`` directory
## using the reference implementation from ``languages/source.nim``. This
## makes sure the reference implementation works as expected.

import
  std/[os, strutils, strscans, streams, parsecfg, options, math],
  languages/source,
  passes/[syntax_source, trees],
  phy/tree_parser,
  spec/[bignums, interpreter, langdefs, rationals]

import spec/types except Node

type
  Node = types.Node[TypeId]
  TestSpec = object
    ## Partially parsed test specification.
    outputs: seq[string]
    deduceOnly: bool
    reject: bool

const
  defaultCtx = term C(symbols: {:}, ret: VoidTy())
    ## the initial context to pass to `types`
  defaultDynCtx = term(
    DC(locs: {:},
       nloc: 0,
       time: 0,
       output: array(),
       errOutput: array(),
       files: {:}))
    ## the initial dynamic context to pass to `cstep`
  issues = [ # tests that are currently expected to fail
    "t19_write.test",
    "t19_writeErr.test",
    "t20_readFile.test",
    "t20_readFile_missing.test",
    "t22_record_type_equality_1.test"
  ]

var typesRel, cstepRel, toplevelRel, desugarFnc, reduceModFnc = -1

proc parseSpec(spec: sink string, path: string): TestSpec =
  ## Parses the test specification from `spec`; at least the parts relevant
  ## to the tester.
  var parser: CfgParser
  parser.open(newStringStream(spec), path, 1)
  # errors are ignored. The specs are expected to have been already validated
  # during the ``tester`` run
  while true:
    let evt = parser.next()
    case evt.kind
    of cfgEof:
      break
    of cfgKeyValuePair:
      var i = 0
      if evt.key.scanf("output.$i$.", i):
        if i >= result.outputs.len:
          result.outputs.grow(i + 1, "")
        result.outputs[i] = evt.value
      elif evt.key == "output":
        result.outputs.add evt.value
      elif evt.key == "reject":
        result.reject = parseBool(evt.value)
      elif evt.key == "arguments":
        if evt.value == "c":
          result.deduceOnly = true
    else:
      discard "ignore"

  parser.close()

template sym(s: string): Node = Node(kind: nkSymbol, sym: s)

proc convertFloat(f: float): Node =
  ## Converts a floating-point value to the representation used by the
  ## specification (refer to to the `float` type in ``source.nim``).
  # 1-bit sign, 11-bit biased exponent, 52-bit mantissa
  const Bias = 1022 + 53
  case classify(f)
  of fcNormal:
    let
      bits = cast[uint64](f)
      exp = int((bits shr 52) and 0x7FF) - Bias # unbias the exponent
      m = (bits and 0xF_FFFF_FFFF_FFFF'u64) + (1 shl 52) # add the implied bit
      s = if f < 0.0: Node(kind: nkTrue) else: Node(kind: nkFalse)
    tree(nkConstr, sym("Finite"), s,
      Node(kind: nkNumber, num: rational(m)),
      Node(kind: nkNumber, num: rational(exp)))
  of fcSubnormal:
    let
      bits = cast[uint64](f)
      exp = -1074
      m = (bits and 0xF_FFFF_FFFF_FFFF'u64) # no implied bit
      s = if f < 0.0: Node(kind: nkTrue) else: Node(kind: nkFalse)
    tree(nkConstr, sym("Finite"), s,
      Node(kind: nkNumber, num: rational(m)),
      Node(kind: nkNumber, num: rational(exp)))
  of fcZero:
    tree(nkConstr, sym("Zero"), Node(kind: nkFalse))
  of fcNegZero:
    tree(nkConstr, sym("Zero"), Node(kind: nkTrue))
  of fcNan:
    tree(nkConstr, sym("Nan"))
  of fcInf:
    tree(nkConstr, sym("Inf"), Node(kind: nkFalse))
  of fcNegInf:
    tree(nkConstr, sym("Inf"), Node(kind: nkTrue))

proc convert(tree: PackedTree[syntax_source.NodeKind], n: NodeIndex): Node =
  ## Converts the packed-tree representation to the semantically equivalent
  ## meta-language representation.
  case tree[n].kind
  of IntVal:
    tree(nkConstr,
      sym("IntVal"),
      Node(kind: nkNumber, num: rational(tree.getInt(n))))
  of FloatVal:
    tree(nkConstr,
      sym("FloatVal"),
      convertFloat(tree.getFloat(n)))
  of StringVal:
    tree(nkConstr,
      sym("StringVal"),
      Node(kind: nkString, sym: tree.getString(n)))
  of Ident:
    tree(nkConstr,
      sym("Ident"),
      Node(kind: nkString, sym: tree.getString(n)))
  elif tree[n].kind.isAtom:
    tree(nkConstr, sym($tree[n].kind))
  else:
    var r = tree(nkConstr, sym($tree[n].kind))
    for it in tree.items(n):
      r.add convert(tree, it)
    r

proc add(res: var string, n: Node) =
  ## Appends the pretty-printed S-expression representation of `n` to `res`.
  case n.kind
  of nkConstr:
    if n[0].sym == "IntVal":
      res.add n[^1]
    elif n[0].sym == "FloatVal":
      res.add n[^1]
    elif n[0].sym == "Inf":
      if n[1].kind == nkTrue:
        res.add "-inf"
      else:
        res.add "inf"
    elif n[0].sym == "Nan":
      res.add "nan"
    elif n[0].sym == "Zero":
      if n[1].kind == nkTrue:
        res.add "-"
      res.add "0.0"
    elif n[0].sym == "Finite":
      var tmp = float(n[2].num.toInt.toInt) *
                pow(2, float(n[3].num.toInt.toInt))
      if n[1].kind == nkTrue:
        tmp = -tmp
      res.addFloat tmp
    elif n[0].sym == "proc":
      res.add "(proc ...)"
    elif n[0].sym == "Ident":
      res.add n[^1].sym
    else:
      res.add "("
      for i, it in n.children.pairs:
        if i > 0:
          res.add ' '
        res.add it
      res.add ")"
  of nkNumber:
    res.addRat n.num
  of nkSymbol:
    res.add n.sym
  of nkString:
    res.add escape(n.sym)
  else:
    doAssert false, "unreachable"

proc `$`(n: Node): string =
  result.add(n)

proc applyFunc(id: int, n: sink Node): Option[Node] =
  ## Generic function application.
  let e = interpret(lang, tree(nkCall, Node(kind: nkFunc, id: id), n))
  if e.kind == nkFail:
    none(Node)
  else:
    some(e)

proc applyRelation(id: int, n: sink Node): Option[Node] =
  ## Generic relation application.
  try:
    let e = interpret(lang, tree(nkCall, Node(kind: nkRelation, id: id), n))
    if e.kind == nkFail:
      none(Node)
    else:
      some(e)
  except KeyError:
    none(Node)

proc runTest(e: sink Node, spec: TestSpec): string =
  ## Implements the main testing. Returns an empty string on success.
  template unpack(res: Option[Node], msg: string): Node =
    var tmp = res
    if tmp.isSome: move tmp.get()
    else:          return msg

  e = applyFunc(desugarFnc, e).unpack("cannot desugar")

  let
    isModule = e.kind == nkConstr and e[0].sym == "Module"
    typ =
      if isModule:
        applyRelation(toplevelRel, tree(nkTuple, defaultCtx, e)).
          map(proc(it: auto): auto = it[1])
      else:
        applyRelation(typesRel, tree(nkTuple, defaultCtx, e))

  if spec.reject:
    if typ.isSome:
      return "expected type check failure, but got: " & $typ.get
    else:
      return ""
  elif typ.isNone:
    return "cannot deduce type"

  if spec.deduceOnly:
    return "" # we're done

  if isModule:
    e = applyFunc(reduceModFnc, e).unpack("cannot reduce module")

  let val = applyRelation(cstepRel, tree(nkTuple, defaultDynCtx, e)).
              unpack("cannot reduce")[1]
  let got = $val & " : " & $typ.get
  if spec.outputs.len == 0:
    if isModule and got == "(Unreachable) : (VoidTy)":
      # XXX: a temporary solution until spectest gets integrated into the
      #      real test runner
      discard "ignored"
    else:
      result = "an output specification is missing for the test"
  elif spec.outputs[^1] != got:
    result = "expected '" & spec.outputs[^1] & "', but got '" & got & "'"

# gather the indices of the relations we need later:
for i, it in lang.relations.pairs:
  case it.name
  of "mtypes":
    # use mtypes instead of types to strip the mutability qualifier from types
    typesRel = i
  of "cstep":
    cstepRel = i
  of "toplevel":
    toplevelRel = i

for i, it in lang.functions.pairs:
  case it.name
  of "desugar":
    desugarFnc = i
  of "reduceModule":
    reduceModFnc = i

if typesRel == -1:
  quit "missing 'mtypes' relation"
if cstepRel == -1:
  quit "missing 'cstep' relation"
if toplevelRel == -1:
  quit "missing 'toplevel' relation"
if desugarFnc == -1:
  quit "missing 'desugar' function"
if reduceModFnc == -1:
  quit "missing 'reduceModule' function"

var total, successful = 0

# the expectation is that the executable is located in the directory containing
# the tests
for (kind, path) in walkDir(getAppDir(), relative=true):
  if kind == pcFile and path.endsWith(".test"):
    var s = newFileStream(getAppDir() / path, fmRead)
    var spec: TestSpec
    if s.readLine() == "discard \"\"\"":
      # extract the specification:
      var text = ""
      while (let line = s.readLine(); line != "\"\"\""):
        text.add line

      spec = parseSpec(text, path)
    else:
      s.setPosition(0)
      spec = TestSpec(outputs: @[], reject: false)

    let
      e = convert(fromSexp[syntax_source.NodeKind](s.readAll()), NodeIndex(0))
      err = runTest(e, spec)

    if err != "":
      if path notin issues:
        echo "test failed: ", path
        echo err
        programResult = 1
      # else: failure is expected
    else:
      inc successful
      if path in issues:
        echo "expected problem with '", path, "', but there was none"
        programResult = 1

    inc total

echo "ran ", total, " tests; ", successful, " were succesful"
