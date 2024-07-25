## Implements a test driver program. If invoked without any arguments, it acts
## as the "driver process", spawning an instance of itself for every test file
## there is.
##
## If invoked with a test file path as an argument, parses the specification,
## invokes the runner for said test file, and then makes sure the runner
## execution result matches the specification.

import
  std/[
    options,
    parseopt,
    parsecfg,
    os,
    osproc,
    strutils,
    streams
  ],
  experimental/[
    colortext
  ]

type
  OutputSpec = object
    fromFile: bool
      ## whether the expected output is provided by a file
    output: string
      ## either a file path or the expected output

  TestSpec = object
    ## A test specification. Contains information about a test and what to
    ## expect from it.
    expected: seq[OutputSpec]
      ## the output(s) expected from the runner (if any)
    knownIssue: Option[string]
      ## whether the test is currently expected to fail due to a known issue

  ResultKind = enum
    rkSuccess
    rkError
    rkMismatch
    rkUnexpectedSuccess

  TestResult = object
    ## The result of a single test run.
    case kind: ResultKind
    of rkSuccess, rkUnexpectedSuccess:
      discard
    of rkError:
      output: string
    of rkMismatch:
      got, expected: string

proc exec(cmd: string, args: openArray[string]): tuple[output: string,
                                                       code: int] =
  ## Similar to ``execProcess``, but also returns the exit code.
  let
    p = startProcess(cmd, args=args, options={poUsePath, poStdErrToStdOut})
    stream = p.outputStream
  var buf: array[128, char]
  # drain the stream until the process has finished:
  while p.running:
    let len = readData(stream, addr buf[0], buf.len)
    if len > 0:
      let start = result.output.len
      result.output.setLen(start + len)
      copyMem(addr result.output[start], addr buf[0], len)

  result.code = p.peekExitCode()
  p.close()

proc content(s: OutputSpec): string =
  ## Returns the string to compare the actual runner output against.
  if s.fromFile:
    let f = open(s.output, fmRead)
    defer: f.close()
    readAll(f)
  else:
    s.output

proc compare(res: tuple[output: string, code: int], spec: TestSpec): TestResult =
  ## Compares the runner output `res` against the `spec`.
  if res.code == 0:
    var i = 0
    for got in split(res.output, "!BREAK!"):
      if i < spec.expected.len:
        let expect = content(spec.expected[i])
        if got != expect:
          return TestResult(kind: rkMismatch, got: got, expected: expect)

      inc i

    if i >= spec.expected.len:
      # more output fragments being provided than there exist expectations for
      # is fine
      result = TestResult(kind: rkSuccess)
    else:
      # not enough output fragments
      result = TestResult(kind: rkMismatch, got: "",
                          expected: content(spec.expected[i]))
  else:
    result = TestResult(kind: rkError, output: res.output)

var
  nimExe = findExe("nim")
  runner = ""
  file   = ""

block:
  var opts = initOptParser(getExecArgs())
  while true:
    opts.next()
    if opts.kind != cmdEnd and file != "":
      echo "found trailing: ", opts.cmdLineRest
      quit(1)

    case opts.kind
    of cmdLongOption, cmdShortOption:
      case opts.key
      of "nim":
        nimExe = opts.val
      of "runner":
        runner = opts.val
      else:
        echo "unknown option: ", opts.key
    of cmdArgument:
      file = opts.key
    of cmdEnd:
      break

let currDir = getCurrentDir()

if file.len == 0:
  # the process is the test driver
  let testDir = currDir / "tests"
  var dirs: seq[tuple[path: string, runnerExe: string]]

  # discover all test directories and build the associated runner
  # executables:
  for it in walkDir(testDir, relative=false):
    if it.kind == pcDir:
      let runner = it.path / "runner.nim"
      if fileExists(runner):
        let
          name = it.path.relativePath(testDir) & "_runner"
          exe = changeFileExt("build" / "tests" / name, ExeExt)

        stdout.write("[Building] " & runner.relativePath(currDir) & "... ")
        # build the tester with optimizations
        let p = exec(nimExe, ["c", "--opt:speed", "--path:.",
                              "--nimcache:build/tests/cache/" & name,
                              "-o:" & exe, runner])
        if p.code == 0:
          stdout.writeLine("Success" + fgGreen)
        else:
          stdout.writeLine("Failure" + fgRed)
          stdout.write(p.output)
          quit(1)

        dirs.add (it.path, exe)

  stdout.flushFile()

  var
    total = 0
    success = 0
  # now run the tests:
  # XXX: concurrent execution of the processes is currently not possible,
  #      as they'd clobber each others' output
  for (dir, exe) in dirs.items:
    for it in walkDir(dir, relative=false):
      if it.path.endsWith(".test"):
        inc total
        let p =
          startProcess(getAppFilename(),
                       args=["--runner:" & exe, it.path.relativePath(currDir)],
                       options={poParentStreams})
        if p.waitForExit() == 0:
          inc success
        p.close()

  if success == total:
    echo "Success! Ran ", success, " tests"
  else:
    echo "Failure"
    quit(1)
else:
  echo "[Testing] " + fgCyan, file
  let s = newFileStream(file, fmRead)
  if s.isNil:
    echo "cannot open test file"
    quit(1)

  var spec: TestSpec

  block:
    # check for and register files storing expected output
    let expectedFile = changeFileExt(file, "expected")
    if fileExists(expectedFile):
      spec.expected.add OutputSpec(fromFile: true, output: expectedFile)

  # parse the specification, if any:
  if s.readLine() == "discard \"\"\"":
    var lines: string
    while true:
      lines.add s.readLine()
      if lines.endsWith("\"\"\""):
        lines.setLen(lines.len - 3)
        break
    s.close()

    var parser: CfgParser
    open(parser, newStringStream(lines), file, 1)
    while true:
      let evt = parser.next()
      case evt.kind
      of cfgKeyValuePair:
        case evt.key
        of "description":
          discard "ignored; only exists for informative purposes"
        of "knownIssue":
          spec.knownIssue = some evt.value
        of "output":
          spec.expected.add:
            OutputSpec(fromFile: false,
                       output: strip(evt.value, leading=true, trailing=false))
        else:
          echo "unknown key: ", evt.key
          quit(1)
      of cfgSectionStart, cfgOption:
        discard "ignore"
      of cfgError:
        echo "Parsing error: ", evt.msg
        quit(1)
      of cfgEof:
        break

    parser.close()
  else:
    s.close()

  # execute the runner and check the output:
  var res = compare(exec(runner, [file]), spec)

  # handle the "known issue" specification:
  if spec.knownIssue.isSome:
    case res.kind
    of rkSuccess:
      res = TestResult(kind: rkUnexpectedSuccess)
    else:
      res = TestResult(kind: rkSuccess)

  # output the test result:
  if res.kind == rkSuccess:
    echo "[Success] " + fgGreen, file
  else:
    echo "[Failure] " + fgRed, file
    programResult = 1

  case res.kind:
  of rkSuccess: discard
  of rkError:
    echo "The runner reported an error:" + fgYellow
    echo res.output
  of rkMismatch:
    echo "Got:" + fgYellow
    echo res.got
    echo "Expected:" + fgYellow
    echo res.expected
  of rkUnexpectedSuccess:
    echo "The test was expected to fail, but it didn't" + fgYellow
