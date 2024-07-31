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
# TODO: output the *difference* (as an S-expression) instead; it's much easier
#       to process for the human reader
writeFile(changeFileExt(args[^1], "expected"), treeRepr(tree))
stdout.write(treeRepr(tree))

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
