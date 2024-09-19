## A tool that extracts the language grammars from Markdown files, verifies
## that the grammar and diffs are sound, and generates the run-time
## verification logic and type definitions (if requested).

import
  std/[os, tables],
  experimental/[colortext],
  sem, checksgen

proc main(args: openArray[string]) =
  if args.len < 3:
    echo "usage: passtool <cmd> <dir> <langname> ..."
    quit(1)

  var
    langs: Languages
    errors: Errors

  # parse and analyse the provided file:
  sem(args[2], args[1], langs, errors)
  trim(langs, errors)

  if errors.hasErrors:
    for source, it in errors.items:
      echo source, " [Error] " + fgRed, it

    quit(1)

  case args[0]
  of "verify":
    discard "done already"
  of "gen-checks":
    if args.len != 5:
      echo "usage: passtool <dir> <langname> gen-checks <module> <out-file>"
      quit(1)

    writeFile(args[4], gen(langs[args[2]], args[3]))
  else:
    echo "unknown command: ", args[0]
    quit(1)

  # TODO: implement the rest of the passtool's features, such as the code
  #       generation mentioned above

main(getExecArgs())
