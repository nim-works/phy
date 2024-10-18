## The test runner for asm.js tests.

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
    asmjs,
    spec,
    trees
  ]

let args = getExecArgs()
let s = openFileStream(args[^1], fmRead)
# skip the test specification:
if s.readLine() == "discard \"\"\"":
  while not s.readLine().endsWith("\"\"\""):
    discard
else:
  s.setPosition(0)

let f = translate(fromSexp[NodeKind](parseSexp("(Module " & readAll(s) & ")")))
writeFile("test.js", f)

# run the test with Node.js:
if execShellCmd("node " & (getCurrentDir() / "test.js")) != 0:
  quit(1)
