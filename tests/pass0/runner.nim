## The test runner for the pass0 tests. Parses the test files content, invokes
## pass0 with it, and runs the resulting code with the VM.
##
## For the convenience of writing tests, the top-level ``Module`` node is
## inserted by the tester.

import
  std/[
    os,
    streams,
    strutils
  ],
  experimental/[
    sexp
  ],
  common/[
    vmexec
  ],
  generated/[
    lang0_checks
  ],
  passes/[
    debugutils,
    pass0,
    spec,
    trees
  ],
  vm/[
    disasm,
    utils,
    vm,
    vmenv,
    vmvalidation,
    vmtypes
  ]

let args = getExecArgs()
let s = openFileStream(args[^1], fmRead)
# skip the test specification:
if s.readLine() == "discard \"\"\"":
  while not s.readLine().endsWith("\"\"\""):
    discard
else:
  s.setPosition(0)

let tree = fromSexp[NodeKind](parseSexp("(Module " & readAll(s) & ")"))
s.close()

checkSyntax(tree, lang0_checks, top)

var env = initVm(1024, 1024 * 1024)
translate(tree, env)

# make sure the environment is correct:
let errors = validate(env)
if errors.len > 0:
  for it in errors.items:
    echo it
  echo "validation failure"
  quit(1)

# output the disassembled code:
stdout.write(disassemble(env))
stdout.write("!BREAK!")

# don't run the code if explicitly disabled:
if args.len > 1 and args[0] == "--noRun":
  stdout.write("(Done)")
  quit(0)

# output it:
stdout.write(run(env, env.procs.high.ProcIndex))
