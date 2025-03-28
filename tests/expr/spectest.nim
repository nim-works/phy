## Temporary test orchestrator that runs all tests in the ``expr`` directory
## using the reference implementation from ``languages/source.nim``. This
## makes sure the reference implementation works as expected.

import
  std/[os, strutils, strscans, streams, parsecfg, options],
  languages/source,
  passes/[syntax_source, trees],
  phy/tree_parser,
  spec/[interpreter, langdefs, rationals]

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
    "t02_add_float_values.test",
    "t02_sub_float_values.test",
    "t04_empty_module.test",
    "t04_proc_declaration.test",
    "t04_type_declaration.test",
    "t04_type_declaration_no_self_visibility.test",
    "t05_empty_return_type_mismatch.test",
    "t05_proc_with_bool_return_type.test",
    "t05_proc_with_float_return_type.test",
    "t05_proc_with_int_return_type.test",
    "t05_proc_with_non_void_body.test",
    "t05_proc_with_non_void_body_error.test",
    "t05_proc_with_non_void_body_subtype.test",
    "t05_proc_with_union_return_type.test",
    "t05_return_operand_cannot_be_void.test",
    "t05_return_type_mismatch.test",
    "t05_unreachable_is_void.test",
    "t06_call_lookup_error.test",
    "t06_call_lookup_self_visible.test",
    "t06_call_proc_with_bool_return_type.test",
    "t06_call_proc_with_float_return_type.test",
    "t06_call_proc_with_int_return_type.test",
    "t06_call_proc_with_tuple_return_type.test",
    "t06_call_proc_with_unit_return_type.test",
    "t06_call_proc_with_void_return_type.test",
    "t06_call_result_field_access.test",
    "t06_declared_type_usage.test",
    "t06_disallowed_void_in_union.test",
    "t06_redeclaration_error_1.test",
    "t06_redeclaration_error_2.test",
    "t06_redeclaration_error_3.test",
    "t09_decl_void_error.test",
    "t11_scopes_local_cannot_shadow_error_1.test",
    "t11_scopes_procdef.test",
    "t13_proc_type_mismatch_error.test",
    "t13_proc_type_void_parameter_error.test",
    "t13_proc_value_1.test",
    "t13_proc_value_2.test",
    "t13_proc_value_3.test",
    "t13_usage_in_return.test",
    "t14_parameters_aggregate_1.test",
    "t14_parameters_aggregate_2.test",
    "t14_parameters_aggregate_3.test",
    "t14_parameters_eval_order_1.test",
    "t14_parameters_eval_order_2.test",
    "t14_parameters_immutable_1_error.test",
    "t14_parameters_immutable_2_error.test",
    "t14_parameters_immutable_3_error.test",
    "t14_parameters_primitive_1.test",
    "t14_parameters_primitive_2.test",
    "t14_parameters_redeclaration_1_error.test",
    "t14_parameters_redeclaration_2_error.test",
    "t14_parameters_void_error.test",
    "t14_parameters_scoping.test",
    "t15_while_true.test",
    "t15_while_true_complex_error.test",
    "t16_seq_construct_with_void_error.test",
    "t16_seq_type_with_void_error.test",
    "t17_seq_concat_to_empty.test",
    "t17_seq_concat_to_non_empty.test",
    "t17_seq_copy_4.test",
    "t18_seq_character_string_1.test",
    "t18_seq_character_string_2.test",
    "t19_write.test",
    "t19_writeErr.test",
    "t20_readFile.test",
    "t20_readFile_missing.test",
  ]

var typesRel, cstepRel, desugarFnc = -1

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

proc convert(tree: PackedTree[syntax_source.NodeKind], n: NodeIndex): Node =
  ## Converts the packed-tree representation to the semantically equivalent
  ## meta-language representation.
  case tree[n].kind
  of IntVal:
    tree(nkConstr,
      Node(kind: nkSymbol, sym: "IntVal"),
      Node(kind: nkNumber, num: rational(tree.getInt(n))))
  of FloatVal:
    # TODO: +/-inf and +/-nan need to be handled properly. This first requires
    #       proper support for both in the reference implementation
    tree(nkConstr,
      Node(kind: nkSymbol, sym: "FloatVal"),
      Node(kind: nkNumber, num: rational(tree.getFloat(n))))
  of Ident:
    tree(nkConstr,
      Node(kind: nkSymbol, sym: "Ident"),
      Node(kind: nkString, sym: tree.getString(n)))
  elif tree[n].kind.isAtom:
    tree(nkConstr, Node(kind: nkSymbol, sym: $tree[n].kind))
  else:
    var r = tree(nkConstr, Node(kind: nkSymbol, sym: $tree[n].kind))
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
      let tmp = $n[^1].num
      res.add tmp
      if '.' notin tmp:
        # rendered float values must always contain a dot
        res.add ".0"
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

proc desugar(n: Node): Option[Node] =
  ## Returns the desugared version of source language expression `n`.
  let e = tree(nkCall, Node(kind: nkFunc, id: desugarFnc), n)
  try:
    some(interpret(lang, e)[0])
  except Failure:
    none(Node)

proc types(n: Node): Option[Node] =
  ## Searches for the type the `types` relation relates `n` to. Returns none
  ## if there there exists no corresponding type.
  let e = tree(nkCall, Node(kind: nkRelation, id: typesRel),
               tree(nkTuple, defaultCtx, n))
  try:
    some(interpret(lang, e)[0])
  except Failure, KeyError:
    none(Node)

proc eval(n: Node): Option[Node] =
  ## Searches for and returns the irreducible expression `n` reduces to.
  let e = tree(nkCall, Node(kind: nkRelation, id: cstepRel),
               tree(nkTuple, defaultDynCtx, n))
  try:
    some(interpret(lang, e)[0][1])
  except Failure, KeyError:
    none(Node)

# gather the indices of the relations we need later:
for i, it in lang.relations.pairs:
  case it.name
  of "mtypes":
    # use mtypes instead of types to strip the mutability qualifier from types
    typesRel = i
  of "cstep":
    cstepRel = i

for i, it in lang.functions.pairs:
  case it.name
  of "desugar":
    desugarFnc = i

if typesRel == -1:
  quit "missing 'mtypes' relation"
if cstepRel == -1:
  quit "missing 'cstep' relation"
if desugarFnc == -1:
  quit "missing 'desugar' function"

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
      desugared = desugar(e)

    var success = false
    var msg = ""
    if desugared.isSome:
      let
        e {.cursor.} = desugared.get
        typ = types(e)
      if spec.reject:
        success = typ.isNone
        if not success:
          msg = "expected type check failure, but got: " & $typ.get
      else:
        if typ.isSome:
          if spec.deduceOnly:
            success = true
          else:
            let val = eval(e)
            if val.isSome:
              let got = ($val.get & " : " & $typ.get)
              if spec.outputs[^1] == got:
                success = true
              else:
                msg = "expected '" & spec.outputs[^1] & "', but got '" & got & "'"
            else:
              msg = "cannot reduce"
        else:
          msg = "cannot deduce type"
    else:
      msg = "cannot desugar"

    if not success:
      if path notin issues:
        echo "test failed: ", path
        echo msg
        programResult = 1
      # else: failure is expected
    else:
      inc successful
      if path in issues:
        echo "expected problem with '", path, "', but there was none"
        programResult = 1

    inc total

echo "ran ", total, " tests; ", successful, " were succesful"
