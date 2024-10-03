## The test runner for the pass10 tests.

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
    lang7_checks,
    lang10_checks
  ],
  passes/[
    changesets,
    debugutils,
    pass0,
    pass1,
    pass3,
    pass4,
    pass7,
    pass10,
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

checkSyntax(tree, lang10_checks, top)
tree = tree.apply(pass10.lower(tree))
checkSyntax(tree, lang7_checks, top)

# output the lowered code:
stdout.writeLine(pretty(tree, tree.child(0)))
stdout.writeLine(pretty(tree, tree.child(1)))
stdout.writeLine(pretty(tree, tree.child(2)))
stdout.write("!BREAK!")

# apply the remaining lowerings:
tree = tree.apply(pass7.lower(tree))
tree = tree.apply(pass4.lower(tree))
tree = tree.apply(pass3.lower(tree, 8))
tree = tree.apply(pass1.lower(tree, 8))

# translate to VM bytecode:
var env = initVm(1024, 1024 * 1024)
translate(tree, env)

if args.len == 2 and args[0] == "--compileOnly":
  # don't check or run anything
  stdout.write("(Done)")
  quit(0)

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

case res.kind
of yrkDone:
  stdout.write("(Done)")
of yrkUnhandledException:
  stdout.write("(UnhandledException " & $res.exc.intVal & ")")
of yrkError:
  stdout.write("(Error " & $res.error & ")")
else:
  echo "unexpected result, but got: ", res
  quit(1)
