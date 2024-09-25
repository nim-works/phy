## Test runner for source language specification tests.

import
  std/[
    os,
    streams,
    strutils
  ],
  experimental/[
    sexp
  ],
  generated/[
    source_checks,
    lang10_checks
  ],
  passes/[
    debugutils,
    changesets,
    pass0,
    pass1,
    pass3,
    pass4,
    pass10,
    source2il,
    spec_source,
    trees
  ],
  phy/[
    default_reporting,
    types
  ],
  common/[
    vmexec
  ],
  vm/[
    vmenv,
    vmvalidation
  ]

let
  args = getExecArgs()
  s = openFileStream(args[^1], fmRead)

# skip the test specification:
if s.readLine() == "discard \"\"\"":
  while not s.readLine().endsWith("\"\"\""):
    discard
else:
  s.setPosition(0)

let input = fromSexp[NodeKind](parseSexp(readAll(s)))
s.close()

# -------------------
# translate the input

var reporter = initDefaultReporter[string]()
var ctx = source2il.open(reporter)

case input[NodeIndex(0)].kind
of DeclNodes:
  # it's a single declaration
  checkSyntax(input, source_checks, decl)
  ctx.declToIL(input, NodeIndex(0))
of ExprNodes:
  # it's a standalone expression
  checkSyntax(input, source_checks, expr)
  discard ctx.exprToIL(input)
of Module:
  # it's a full module. Translate all declarations
  checkSyntax(input, source_checks, module)
  for it in input.items(NodeIndex(0)):
    ctx.declToIL(input, it)

  # the last procedure is the one that will be executed
else:
  echo "unexpected node: ", input[NodeIndex(0)].kind
  quit(1)

# don't continue if there was an error:
let messages = reporter[].retrieve()
if messages.len > 0:
  for it in messages.items:
    echo "Error: ", it
  quit(2)

# it's possible that there aren't any procedures
let typ =
  if ctx.procList.len > 0:
    ctx.procList[^1].result
  else:
    prim(tkVoid)

# ---------------
# apply lowerings

var tree = close(ctx)
checkSyntax(tree, lang10_checks, top)

# lower to the L0 language:
tree = tree.apply(pass10.lower(tree))
tree = tree.apply(pass4.lower(tree))
tree = tree.apply(pass3.lower(tree, 8))
tree = tree.apply(pass1.lower(tree, 8))

# generate the bytecode:
var env = initVm(1024, 1024 * 1024)
translate(tree, env)

# make sure the environment is correct:
let errors = validate(env)
if errors.len > 0:
  for it in errors.items:
    echo it
  echo "validation failure"
  quit(1)

if env.procs.len > 0:
  # execute the trailing procedure and echo the result:
  stdout.write run(env, env.procs.high.ProcIndex, typ)
