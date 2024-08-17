## Test runner for source language expression tests.

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
    source2il,
    spec_source,
    trees
  ],
  vm/[
    vm,
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

# parse the S-expression and translate the source language to the L1:
var (typ, tree) = exprToIL(fromSexp[NodeKind](parseSexp(readAll(s))))
# lower to the L0 language:
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

# run the code:
var
  thread = vm.initThread(env, env.procs.high.ProcIndex, 1024, @[])
  res = run(env, thread, nil)
env.dispose(move thread)

if res.kind != yrkDone:
  echo "failed with: ", res
  quit(1)

# echo the result:
case typ
of tkInt:
  stdout.write($res.result.intVal & ": int")
of tkFloat:
  stdout.write($res.result.floatVal & ": float")