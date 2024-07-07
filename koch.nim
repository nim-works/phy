## Tool for performing various build and testing related actions for the
## repository. *Koch* is a German noun meaning *cook* or *chef* in English.

import std/[sequtils, strutils, os, osproc, parseopt]

const
  HelpText = """
Usage:
  build [options] <command>

Options:
  --nim:path                  use the specified NimSkull compiler

Commands:
  all [args]                  builds all programs
  single <name> [args]        builds the single program with the given name
"""
  Programs: seq[(string, string)] = @[]

var
  nimExe = findExe("nim")
  verbose = true

proc compile(file: sink string, name: string, extra: varargs[string]): bool =
  ## Compiles the given NimSkull `file` into an exectuable located in the bin/
  ## directory, using `name` as the name.
  var args = @["c", "--nimcache:build/cache/" & name,
               "-o:bin/" & addFileExt(name, ExeExt)]
  args.add extra
  args.add file
  if verbose:
    echo "run: ", nimExe, " ", args.join(" ")
  let p = startProcess(nimExe, args=args, options={poParentStreams, poUsePath})
  result = p.waitForExit(-1) == 0
  p.close()

proc saneSplit(s: string): seq[string] =
  ## Compared to the normal split, returns an empty sequence for an empty
  ## string.
  let s = strip(s)
  if s.len > 0: split(s, ' ')
  else:         @[]

# command implementations:

proc buildSingle(args: string): bool =
  ## Builds the single program specified by `args`.
  var args = args.saneSplit()
  if args.len == 0:
    return false # not enough arguments, show the help

  let progName = args[0]
  args.delete(0)

  result = true

  for (name, path) in Programs.items:
    if name == progName:
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
  for (name, path) in Programs.items:
    echo extra
    if not compile(getCurrentDir() / path, name, extra):
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
      of "all":    buildAll(opts.cmdLineRest)
      of "single": buildSingle(opts.cmdLineRest)
      of "help":   showHelp()
      else:
        echo "Unknown command: ", normalize(opts.key)
        false
    break
  of cmdEnd:
    break

if not success:
  echo HelpText
  quit(1)
