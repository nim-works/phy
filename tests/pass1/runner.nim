## The test runner for the pass1 tests.

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
    debugutils,
    pass0,
    pass1,
    spec,
    trees
  ],
  vm/[
    vm,
    vmenv,
    vmvalidation,
  ]

let
  args = getExecArgs()
  s    = openFileStream(args[^1], fmRead)

# skip the test specification:
if s.readLine() == "discard \"\"\"":
  while not s.readLine().endsWith("\"\"\""):
    discard
else:
  s.setPosition(0)

var tree = fromSexp[NodeKind](parseSexp("(Module " & readAll(s) & ")"))
s.close()

let transformation = pass1.lower(tree, 8)
tree = tree.apply(transformation)

# output the lowered code:
# TODO: instead of the whole tree, only the *difference* (as an S-expression)
#       should be returned, which would make it easier for a human reader to
#       validate the output
stdout.writeLine(pretty(tree, tree.child(0)))
stdout.writeLine(pretty(tree, tree.child(1)))
stdout.writeLine(pretty(tree, tree.child(2)))

# translate to VM bytecode:
var env = initVm(1024, 1024 * 1024)
translate(tree, env)

# make sure the environment is correct:
let errors = validate(env)
if errors.len > 0:
  for it in errors.items:
    echo it
  echo "validation failure"
  quit(1)

var
  thread = vm.initThread(env, env.procs.high.ProcIndex, 1024, @[])
  res = run(env, thread, nil)
env.dispose(move thread)

if res.kind != yrkDone:
  echo "expected successful execution, but got: ", res
  quit(1)
