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
  passes/[
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

var ctx = source2il.open()
var typ: TypeKind

case input[NodeIndex(0)].kind
of DeclNodes:
  # it's a single declaration
  typ = ctx.declToIL(input, NodeIndex(0))
of ExprNodes:
  # it's a standalone expression
  typ = ctx.exprToIL(input)
of Module:
  # it's a full module. Translate all declarations
  for it in input.items(NodeIndex(0)):
    typ = ctx.declToIL(input, it)
    if typ == tkError:
      break

  # the last procedure is the one that will be executed

  if input.len(NodeIndex(0)) == 0:
    typ = tkVoid # set to something that's not ``tkError``
else:
  echo "unexpected node: ", input[NodeIndex(0)].kind
  quit(1)

# don't continue if there was an error:
if typ == tkError:
  echo "semantic analysis failed"
  quit(2)

# ---------------
# apply lowerings

var tree = close(ctx)
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
