## Implements a CLI for running the various parts that make up Phy. This
## includes the assembler, the various passes, `source2IL <source2il.html>`_,
## and the VM.

import
  std/[
    os,
    parseopt,
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
    lang0_checks,
    lang1_checks,
    lang3_checks,
    lang5_checks,
    lang25_checks,
    lang30_checks,
    source_checks
  ],
  passes/[
    changesets,
    debugutils,
    source2il,
    pass0,
    pass1,
    pass3,
    pass5,
    pass25,
    pass30,
    trees
  ],
  phy/[
    default_reporting,
    types
  ],
  vm/[
    assembler,
    disasm,
    utils,
    vmenv,
    vmvalidation
  ]

# cannot import normally, as some type names would conflict
import passes/spec except NodeKind
import passes/spec_source except NodeKind

type
  Language = enum
    langBytecode = "vm"
    lang0 = "L0"
    lang1 = "L1"
    lang3 = "L3"
    lang5 = "L5"
    lang25 = "L25"
    lang30 = "L30"
    langSource = "source"

  Command = enum
    None
    Compile = "c"
    Eval = "e"

const
  HelpText = """
Usage:
  phy <command> [options] <filename>

Options:
  --source:lang               the language the input file uses
  --target:lang               the language to translate/lower to
  --runner                    makes the program suitable for being used as a
                              test runner

Commands:
  c                           translates/lowers the code from the source
                              language to the target language
  e                           similar to 'c', but also runs the generated
                              bytecode and echoes the result
"""

var
  gShow: set[Language]
    ## the set of languages for which the IR should be printed once available
  gRunner = false
    ## whether the program is used as a test runner. This enables some
    ## accommodations for the tester

proc error(msg: string) =
  echo "Error: ", msg
  quit 1

template syntaxCheck(code: PackedTree, module, name: untyped) {.dirty.} =
  # for some reason, ``checkSyntax`` from ``debugutils`` doesn't want to work
  # within this module
  module.check(code, NodeIndex(0), name):
    if node in code:
      echo "Syntax error: \"", rule, "\" didn't match for child node '", child,
          "' (kind = ", code[node, child].kind, ") of '", ord(node), "'"
    else:
      echo "Syntax error: \"", rule, "\" didn't match. Unexpected end"
    quit(1)

proc syntaxCheck(code: PackedTree[spec.NodeKind], lang: Language) =
  ## Runs the syntax checks for `lang` on `code`, aborting the program with an
  ## error if they don't succeed.
  case lang
  of lang0:  syntaxCheck(code, lang0_checks, module)
  of lang1:  syntaxCheck(code, lang1_checks, module)
  of lang3:  syntaxCheck(code, lang3_checks, module)
  of lang5:  syntaxCheck(code, lang5_checks, module)
  of lang25: syntaxCheck(code, lang25_checks, module)
  of lang30: syntaxCheck(code, lang30_checks, module)
  else:      unreachable()

template genericPrint(lang: Language, body: untyped) =
  let L = lang
  if L in gShow:
    # for the tester, the output is formatted such that it's easy
    # to detect where the end is
    if not gRunner:
      stdout.writeLine("---- " & $L)

    body

    if gRunner:
      stdout.write("!BREAK!")
    else:
      stdout.writeLine("----")

proc print(tree: PackedTree[spec.NodeKind], lang: Language) =
  genericPrint(lang):
    stdout.writeLine(pretty(tree, tree.child(0)))
    stdout.writeLine(pretty(tree, tree.child(1)))
    stdout.writeLine(pretty(tree, tree.child(2)))

proc print(env: VmEnv) =
  genericPrint(langBytecode):
    stdout.write(disassemble(env))

proc sourceToIL(text: string): (PackedTree[spec.NodeKind], SemType) =
  ## Given an S-expression representation of the source language (`text`),
  ## analyzes it and translates it to the highest-level IL. Also returns the
  ## return of the procedure to executre, or ``tkError`` if there is no
  ## procedure to run.
  ##
  ## A failure during analysis aborts the program.
  var code = fromSexp[spec_source.NodeKind](parseSexp(text))

  var reporter = initDefaultReporter[string]()
  var ctx = source2il.open(reporter)

  case code[NodeIndex(0)].kind
  of DeclNodes:
    # it's a single declaration
    syntaxCheck(code, source_checks, decl)
    ctx.declToIL(code, NodeIndex(0))
  of ExprNodes:
    # it's a standalone expression
    syntaxCheck(code, source_checks, expr)
    discard ctx.exprToIL(code)
  of spec_source.NodeKind.Module:
    # it's a full module. Translate all declarations
    syntaxCheck(code, source_checks, module)
    for it in code.items(NodeIndex(0)):
      ctx.declToIL(code, it)

    # the last procedure is the one that will be executed
  else:
    error "unexpected node: " & $code[NodeIndex(0)].kind

  # don't continue if there was an error:
  let messages = reporter[].retrieve()
  if messages.len > 0:
    for it in messages.items:
      echo "Error: ", it
    quit(2)

  result[1] =
    if ctx.procList.len > 0: ctx.procList[^1].result
    else:                    prim(tkError)
  result[0] = ctx.close()

proc compile(tree: var PackedTree[spec.NodeKind], source, target: Language) =
  assert source != langSource
  assert ord(source) >= ord(target)
  var current = source
  while current != target:
    case current
    of lang0, langBytecode, langSource:
      assert false, "cannot be handled here: " & $current
    of lang1:
      syntaxCheck(tree, lang1_checks, module)
      tree = tree.apply(pass1.lower(tree))
      current = lang0
    of lang3:
      syntaxCheck(tree, lang3_checks, module)
      # TODO: don't hardcode the pointer size
      tree = tree.apply(pass3.lower(tree, 8))
      current = lang1
    of lang5:
      syntaxCheck(tree, lang5_checks, module)
      # TODO: don't hardcode the pointer size
      tree = tree.apply(pass5.lower(tree, 8))
      current = lang3
    of lang25:
      syntaxCheck(tree, lang25_checks, module)
      tree = tree.apply(pass25.lower(tree))
      current = lang5
    of lang30:
      syntaxCheck(tree, lang30_checks, module)
      tree = tree.apply(pass30.lower(tree))
      current = lang25

    print(tree, current)

proc main(args: openArray[string]) =
  var opts = initOptParser(args)
  var input = ""

  var source = langSource
  var target = langBytecode

  var cmd = None

  for (kind, key, arg) in opts.getopt():
    case kind
    of cmdShortOption:
      error "unknown option: " & key
    of cmdLongOption:
      case key
      of "runner":
        gRunner = true
      of "source":
        source = parseEnum[Language](arg)
      of "target":
        target = parseEnum[Language](arg)
      of "show":
        gShow.incl parseEnum[Language](arg)
      else:
        error "unknown option: " & key
    of cmdArgument:
      if cmd == None:
        cmd = parseEnum[Command](key)
      else:
        # must be the input filename
        input = key
    of cmdEnd:
      unreachable()

  # make sure the command line arguments are sensible:
  case cmd
  of None:
    echo HelpText
    quit(1)
  of Eval:
    if target != langBytecode:
      error "'e' requires the target language to be '" & $langBytecode & "'"
  else:
    discard "nothing special to do"

  if ord(target) > ord(source):
    error "invalid source and target language pair"

  if input.len == 0:
    error "a filename must be provided"

  var s = openFileStream(input, fmRead)
  if gRunner:
    # skip the test file header, if any
    if s.readLine() == "discard \"\"\"":
      while not s.readLine().endsWith("\"\"\""):
        discard
    else:
      s.setPosition(0)

  let text = s.readAll()
  s.close()

  var
    env = initVm(1024, 1024 * 1024) # 1MB of memory
    code: PackedTree[spec.NodeKind]
    typ: SemType

  if source == langBytecode:
    # run the assembler on the input lines
    var
      a = AssemblerState()
      lineN = 1

    for line in splitLines(text, false):
      try:
        a.process(line, env)
      except AssemblerError as e:
        error input & "(" & $lineN & ", 1): " & e.msg
      inc lineN
  else:
    var newSource = source

    # the input is in some higher-level language
    if source == langSource:
      # translate to the highest-level IL first
      (code, typ) = sourceToIL(text)
      newSource = lang30
      print(code, newSource)
    elif gRunner:
      # in order to reduce visual noise in tests, the ``(Module ...)`` top
      # level node is added implicitly
      code = fromSexp[spec.NodeKind](parseSexp("(Module " & text & ")"))
    else:
      code = fromSexp[spec.NodeKind](parseSexp(text))

    if target == langBytecode:
      # compile to L0 code and then translate to bytecode
      compile(code, newSource, lang0)
      syntaxCheck(code, lang0)
      pass0.translate(code, env)
      # the bytecode is verified later
    else:
      compile(code, newSource, target)
      # make sure the output code is correct:
      syntaxCheck(code, target)

  if target == langBytecode:
    # make sure the environment is correct:
    let errors = validate(env)
    if errors.len > 0:
      echo "Validation of the VM environment failed"
      for it in errors.items:
        echo "Error: ", it
      quit(1)

    print(env)

    # handle the eval command:
    if cmd == Eval:
      if env.procs.len == 0:
        if gRunner:
          discard "okay, silently ignore"
          return
        else:
          error "there's nothing to run"

      if source == langSource:
        # we have type high-level type information
        stdout.write run(env, env.procs.high.ProcIndex, typ)
      else:
        # we don't have high-level type information
        stdout.write run(env, env.procs.high.ProcIndex)

main(getExecArgs())
