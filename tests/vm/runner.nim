## The runner for the VM tests. Runs the last-closed procedure.

import
  std/[
    os,
    streams,
    strutils,
    tables
  ],
  vm/[
    assembler,
    vm,
    vmenv,
    vmmodules,
    vmtypes,
    vmvalidation
  ]

proc test(env: var VmEnv, args: openArray[Value], _: RootRef): CallbackResult =
  ## A VM callback, created for the purpose of testing.
  CallbackResult(code: cecValue, value: args[0])

# 1MB max memory for the VM should be plenty enough for the tests
var
  env   = initVm(1024, 1024 * 1024)
  asmbl = AssemblerState()
  line  = 1

var s = openFileStream(getExecArgs()[0], fmRead)
if s.readLine() == "discard \"\"\"":
  # skip the test specification
  while not s.readLine().endsWith("\"\"\""):
    inc line
  inc line, 2 # one for the start, one for the end
else:
  s.setPosition(0) # move back to the start

# read all lines and pass them to the assembler:
while not s.atEnd:
  try:
    asmbl.process(s.readLine())
    inc line
  except AssemblerError, ValueError:
    stderr.writeLine("In line " & $line & ": " & getCurrentExceptionMsg())
    quit(1)

s.close()

# make sure the assembled module is correct:
let
  module = asmbl.close()
  errors = validate(module)
if errors.len > 0:
  for it in errors.items:
    stderr.writeLine(it)
  quit(1)

var ltab = LinkTable()
if not load(env, ltab, module):
  stderr.write("failed to load module")
  quit(1)

if env.procs.len == 0:
  # there's nothing to execute, but don't treat this as an error
  stdout.write("<no procedures>")
  quit(0)

var
  res: YieldReason
  # use 1KB for the in-memory stack
  thread = env.initThread(env.procs.high.ProcIndex, 1024, @[])

load(env, ltab, toTable({"test": test}))

# run the thread until execution cannot resume anymore:
while true:
  res = run(env, thread, nil)
  case res.kind
  of yrkDone, yrkError, yrkStubCalled, yrkUnhandledException:
    break
  of yrkUser:
    discard "resume after yield"

env.dispose(move thread)

# render and output the result:
var output = "(" & substr($res.kind, 3)
case res.kind
of yrkDone:
  case res.typ
  of tkVoid, tkForeign:
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
  output.add $res.exc
of yrkUser:
  discard "cannot happen"

output.add ")"
# omit the new-line; makes the runner's output more convenient to test
stdout.write(output)
