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
  all [args]                  builds all programs
  single <name> [args]        builds the single program with the given name
  generate [dir]              generates the various language-related modules
"""
  Programs: seq[(string, string, bool)] = @[
    ("tester", "tools/tester.nim", true),
    ("passtool", "tools/passtool/passtool.nim", true),
    ("repl", "tools/repl.nim", false),
    ("phy", "phy/phy.nim", false)
  ]
    ## maps program names to the associated path and whether the program
    ## doesn't depend on generated modules

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
  require run(passtool, "gen-checks", "passes", "lang30", "passes/spec",
              dir / "*_checks.nim")
  require run(passtool, "gen-checks", "spec", "specification",
              "passes/spec_source", dir / "source_checks.nim")

proc buildSingle(args: string): bool

proc regenerate() =
  ## Makes sure the generated modules are up-to-date.
  if not dirExists(DefaultGenerated):
    # assume that the 'generated' folder existing means that it's up-to-date.
    # This is usually *not* correct, but it's the simplest heuristic we have
    discard buildSingle("passtool -d:release")
    generateModules(DefaultGenerated)

# command implementations:

proc buildSingle(args: string): bool =
  ## Builds the single program specified by `args`.
  var args = args.saneSplit()
  if args.len == 0:
    return false # not enough arguments, show the help

  let progName = args[0]
  args.delete(0)

  result = true

  for (name, path, standalone) in Programs.items:
    if name == progName:
      if not standalone:
        # depends on some generated modules; first make sure they're
        # up-to-date
        regenerate()

      if not compile(getCurrentDir() / path, name, args):
        echo "Failure"
        quit(1)
      return

  # report a "not found" error
  echo "no program with name: '", progName, "' exists. Candidates are:"
  echo "  ", mapIt(Programs, it[0]).join(", ")
  quit(1)

proc buildAll(args: string): bool =
  ## Builds all programs, passing `args` along to the compiler.
  let extra = args.saneSplit()
  # build all standalone programs first:
  for (name, path, standalone) in Programs.items:
    if standalone:
      if not compile(getCurrentDir() / path, name, extra):
        echo "Failure"
        quit(1)

  # then generate the language-derived modules:
  generateModules(DefaultGenerated)

  # finally, build the remaining programs:
  for (name, path, standalone) in Programs.items:
    if not standalone:
      if not compile(getCurrentDir() / path, name, extra):
        echo "Failure"
        quit(1)

  result = true

proc generate(args: string): bool =
  ## Invokes the passtool for generating the language-related modules.
  let args = saneSplit(args)
  if args.len > 1:
    echo "too many arguments"
    return false

  # the passtool binary might be out-of-date; it's better to always compile it
  result = buildSingle("passtool -d:release")
  if not result:
    return

  generateModules():
    if args.len == 1: args[0] else: DefaultGenerated

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
      of "all":
        buildAll(opts.cmdLineRest)
      of "single":
        buildSingle(opts.cmdLineRest)
      of "generate":
        generate(opts.cmdLineRest)
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
