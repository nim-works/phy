## A tool that extracts the language grammars from Markdown files, verifies
## that the grammar and diffs are sound, and generates the run-time
## verification logic and type definitions (if requested).

import
  std/[os],
  experimental/[colortext],
  sem

proc main(args: openArray[string]) =
  if args.len != 2:
    echo "usage: passtool <dir> <langname>"
    quit(1)

  var
    langs: Languages
    errors: Errors

  # parse and analyse the provided file:
  sem(args[1], args[0], langs, errors)

  if errors.hasErrors:
    for source, it in errors.items:
      echo source, " [Error] " + fgRed, it

    quit(1)

  # TODO: implement the rest of the passtool's features, such as the code
  #       generation mentioned above

main(getExecArgs())
