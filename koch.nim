## Tool for performing various build and testing related actions for the
## repository. *Koch* is a German noun meaning *cook* or *chef* in English.

import std/[sequtils, strutils, tables, os, osproc, parseopt]

const
  HelpText = """
Usage:
  koch [options] <command>

Options:
  --nim:path                  use the specified NimSkull compiler

Commands:
  build <program> [<arg> ...] builds a program, using the given compiler args
  build all [<arg> ...]       builds all programs
  generate <dir>              generates the various language-related modules
  build-defs                  verifies the language definitions and generates
                              the textual representation for them
"""
  Programs = {
    "tester" : ("tools/tester.nim", true),
    "passtool" : ("tools/passtool/passtool.nim", true),
    "queryshell" : ("phy/queryshell.nim", true),
    "repl" : ("phy/repl.nim", false),
    "phy" : ("phy/phy.nim", false),
    "skully" : ("skully/skully.nim", true),
  }.toOrderedTable
    ## program name, module path, and whether the program doesn't depend on
    ## generated modules

  DefaultGenerated = "generated"
    ## the default path for the generated modules

var
  nimExe = findExe("nim")
  verbose = true

proc run(exe: sink string, args: varargs[string]): bool =
  if verbose:
    echo "run: ", exe, " ", args.join(" ")

  let p = startProcess(exe, args=args, options={poParentStreams, poUsePath})
  result = p.waitForExit(-1) == 0
  p.close()

proc require(x: bool) =
  if not x:
    echo "failure"
    quit(1)

proc compile(file: sink string, name: string, extra: varargs[string]): bool =
  ## Compiles the given NimSkull `file` into an exectuable located in the bin/
  ## directory, using `name` as the name.
  var args = @["c", "--nimcache:build/cache/" & name,
               "-o:bin/" & addFileExt(name, ExeExt)]
  args.add extra
  args.add file
  result = run(nimExe, args)

proc check(file: sink string, extra: varargs[string]): bool =
  ## Runs the ``check`` command on the given NimSkull `file`.
  var args = @["check"]
  args.add extra
  args.add file
  result = run(nimExe, args)

proc saneSplit(s: string): seq[string] =
  ## Compared to the normal split, returns an empty sequence for an empty
  ## string.
  let s = strip(s)
  if s.len > 0: split(s, ' ')
  else:         @[]

# helpers:

proc generateModules(dir: string) =
  ## Invokes the passtool for generating the language-derived modules.
  let passtool = addFileExt("bin/passtool", ExeExt)
  createDir(dir)

  # generate the modules:
  require run(passtool, "gen-checks", "languages", "lang30", "passes/syntax",
              dir / "*_checks.nim")
  require run(passtool, "gen-checks", "languages", "specification",
              "passes/syntax_source", dir / "source_checks.nim")

proc build(name: string, args: openArray[string])

proc regenerate() =
  ## Makes sure the generated modules are up-to-date.
  if not dirExists(DefaultGenerated):
    # assume that the 'generated' folder existing means that it's up-to-date.
    # This is usually *not* correct, but it's the simplest heuristic there is
    build("passtool", ["-d:release"])
    generateModules(DefaultGenerated)

# command implementations:

proc build(name: string, args: openArray[string]) =
  ## Builds the program identified by `name`, passing `args` along to
  ## the compiler.
  if name in Programs:
    let (path, standalone) = Programs[name]
    if not standalone:
      # depends on some generated modules; first make sure they're
      # up-to-date
      regenerate()

    if not compile(getCurrentDir() / path, name, args):
      echo "Failure"
      quit(1)
  else:
    # report a "not found" error
    echo "no program with name: '", name, "' exists. Candidates are:"
    echo "  ", toSeq(Programs.keys).join(", ")
    quit(1)

proc build(names, extra: openArray[string]) =
  ## Builds all programs, passing `args` along to the compiler.
  # build all standalone programs first:
  for name in names.items:
    let (path, standalone) = Programs[name]
    if standalone:
      if not compile(getCurrentDir() / path, name, extra):
        echo "Failure"
        quit(1)

  # then generate the language-derived modules:
  generateModules(DefaultGenerated)

  # finally, build the remaining programs:
  for name in names.items:
    let (path, standalone) = Programs[name]
    if not standalone:
      if not compile(getCurrentDir() / path, name, extra):
        echo "Failure"
        quit(1)

proc build(args: string): bool =
  ## Implements the `build` command.
  let args = args.saneSplit()
  if args.len == 0:
    return false

  case args[0]
  of "all":
    build(toSeq(Programs.keys), args.toOpenArray(1, args.high))
  of "all-ws":
    # ws = without skully
    build(toSeq(Programs.keys).filterIt(it != "skully"),
          args.toOpenArray(1, args.high))
  else:
    build(args[0], args.toOpenArray(1, args.high))

  result = true

proc generate(args: string): bool =
  ## Invokes the passtool for generating the language-related modules.
  let args = saneSplit(args)
  if args.len > 1:
    echo "too many arguments"
    return false

  # the passtool binary might be out-of-date; it's better to always compile it
  build("passtool", ["-d:release"])

  generateModules():
    if args.len == 1: args[0] else: DefaultGenerated

  result = true

proc buildDefs(args: string): bool =
  ## Handles verifying the language definitions and producing the artifacts
  ## based on them.
  if args.len > 0:
    return false

  # there's nothing to do with the compiled language definition, making sure
  # the macro succeeds is enough
  if not check(getCurrentDir() / "languages" / "core.nim"):
    echo "Failure"
    quit(1)

  result = true

proc showHelp(): bool =
  ## Shows the help text.
  echo HelpText
  result = true

# main command processing:
var
  opts = initOptParser(getExecArgs())
  success = false

while true:
  opts.next()
  case opts.kind
  of cmdLongOption, cmdShortOption:
    case normalize(opts.key)
    of "nim":
      nimExe = opts.val
    else:
      echo "Unknown option: ", normalize(opts.key)
      break
  of cmdArgument:
    success =
      case normalize(opts.key)
      of "build":
        build(opts.cmdLineRest)
      of "generate":
        generate(opts.cmdLineRest)
      of "build-defs":
        buildDefs(opts.cmdLineRest)
      of "help":
        showHelp()
      else:
        echo "Unknown command: ", normalize(opts.key)
        false
    break
  of cmdEnd:
    break

if not success:
  echo HelpText
  quit(1)
