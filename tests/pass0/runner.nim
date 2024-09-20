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

var
  thread = vm.initThread(env, env.procs.high.ProcIndex, 1024, @[])
  res = run(env, thread, nil)
env.dispose(move thread)

# XXX: the rendering logic is - for the largest part - the same as for the VM
#      runner. The code should not be duplicated like this
# render the result:
var output = "(" & substr($res.kind, 3)
case res.kind
of yrkDone:
  case env.types[res.typ].kind
  of tkVoid, tkProc, tkForeign:
    discard
  of tkInt:
    output.add " "
    if res.result.uintVal <= high(int64).uint64:
      # the signed and unsigned interpretation yield the same value
      output.addInt res.result.uintVal
    else:
      # output both interpretations
      output.add "(" & $res.result.uintVal & " or " & $res.result.intVal & ")"
  of tkFloat:
    output.add " " & $res.result.floatVal
of yrkError:
  output.add " "
  output.add $res.error
of yrkStubCalled:
  output.add " "
  output.addInt res.stub.int
of yrkUnhandledException:
  output.add " "
  output.addInt res.exc.intVal
of yrkUser:
  unreachable()

output.add ")"
# output it:
stdout.write(output)
