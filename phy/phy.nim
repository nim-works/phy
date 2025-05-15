## Implements a CLI for running the various parts that make up Phy. This
## includes the assembler, the various passes, `source2IL <source2il.html>`_,
## and the VM.

import
  std/[
    options,
    os,
    parseopt,
    streams,
    strutils
  ],
  experimental/[
    sexp
  ],
  generated/[
    lang0_checks,
    langPtr_checks,
    lang1_checks,
    lang2_checks,
    lang3_checks,
    lang4_checks,
    lang5_checks,
    lang6_checks,
    lang25_checks,
    lang30_checks,
    source_checks
  ],
  passes/[
    changesets,
    debugutils,
    source2il,
    pass0,
    pass_aggregateParams,
    pass_aggregatesToBlob,
    pass_flattenPaths,
    pass_globalsToPointer,
    pass_inlineTypes,
    pass_legalizeBlobOps,
    pass_localsToBlob,
    pass_ptrToInt,
    pass_stackAlloc,
    pass25,
    pass30,
    trees
  ],
  phy/[
    default_reporting,
    host_impl,
    tree_parser,
    type_rendering,
    types,
    vmexec
  ],
  vm/[
    assembler,
    disasm,
    utils,
    vmenv,
    vmmodules,
    vmvalidation
  ]

# cannot import normally, as some type names would conflict
import passes/syntax except NodeKind
import passes/syntax_source except NodeKind

when hostOS != "any":
  # unfortunately, skully doesn't support the times and monotimes module yet,
  # meaning that tracing is not supported in a skully-built phy executable
  import phy/tracing
  import std/[tables, times]

type
  Language = enum
    langBytecode = "vm"
    lang0 = "L0"
    langPtr = "LPtr"
    lang1 = "L1"
    lang2 = "L2"
    lang3 = "L3"
    lang4 = "L4"
    lang5 = "L5"
    lang6 = "L6"
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
  --measure                   shows the time various internal processing took
                              as a CSV list on succesful compilation

Commands:
  c                           translates/lowers the code from the source
                              language to the target language
  e                           similar to 'c', but also runs the generated
                              bytecode and echoes the result
"""
  PointerSize = 8
    ## the byte-width of pointer values
    # TODO: this size needs to be configurable from the outside

var
  gShow: set[Language]
    ## the set of languages for which the IR should be printed once available
  gRunner = false
    ## whether the program is used as a test runner. This enables some
    ## accommodations for the tester
  gMeasure = false
    ## whether instrumentation of various is enabled

when declared(EventLog):
  var
    gEvents = initLog()
      ## global performance event log

proc error(msg: string) =
  echo "Error: ", msg
  quit 1

template measure(name: static string, body: untyped) =
  ## Records a ``Start`` and ``Stop`` event around `body`, with `name` as
  ## the data.
  when declared(gEvents):
    gEvents.begin(name)
  body
  when declared(gEvents):
    gEvents.stop(name)

when declared(EventLog):
  proc dumpTimings(log: EventLog) =
    ## Echoes the timings collected in `log` to the standard output, as a
    ## comma-separated-value list.
    var times: Table[string, Duration]
    for it in log.events.items:
      case it.kind
      of Start:
        times[it.data] = log.relative(it)
      of End:
        let diff = log.relative(it) - times[it.data]
        # the time is shown in seconds, using microsecond precision
        echo it.data, ",", float64(inMicroseconds(diff)) / 1e6
      of Action:
        discard "ignore"

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

proc syntaxCheck(code: PackedTree[syntax.NodeKind], lang: Language) =
  ## Runs the syntax checks for `lang` on `code`, aborting the program with an
  ## error if they don't succeed.
  case lang
  of lang0:  syntaxCheck(code, lang0_checks, module)
  of langPtr:syntaxCheck(code, langPtr_checks, module)
  of lang1:  syntaxCheck(code, lang1_checks, module)
  of lang2:  syntaxCheck(code, lang2_checks, module)
  of lang3:  syntaxCheck(code, lang3_checks, module)
  of lang4:  syntaxCheck(code, lang4_checks, module)
  of lang5:  syntaxCheck(code, lang5_checks, module)
  of lang6:  syntaxCheck(code, lang6_checks, module)
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

proc print(tree: PackedTree[syntax.NodeKind], lang: Language) =
  genericPrint(lang):
    stdout.writeLine(pretty(tree, tree.child(0)))
    stdout.writeLine(pretty(tree, tree.child(1)))
    stdout.writeLine(pretty(tree, tree.child(2)))

proc print(m: VmModule) =
  genericPrint(langBytecode):
    stdout.write(disassemble(m))

proc sourceToIL(text: string): (PackedTree[syntax.NodeKind], SemType) =
  ## Given an S-expression representation of the source language (`text`),
  ## analyzes it and translates it to the highest-level IL. Also returns the
  ## return of the procedure to executre, or ``tkError`` if there is no
  ## procedure to run.
  ##
  ## A failure during analysis aborts the program.
  var code = fromSexp[syntax_source.NodeKind](text)

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
  of syntax_source.NodeKind.Module:
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
    if ctx.entry != -1: ctx.procList[ctx.entry].typ.elems[0]
    else:               prim(tkError)
  result[0] = ctx.close()

proc compile(tree: var PackedTree[syntax.NodeKind], source, target: Language) =
  assert source != langSource
  assert ord(source) >= ord(target)
  var current = source
  while current != target:
    case current
    of lang0, langBytecode, langSource:
      assert false, "cannot be handled here: " & $current
    of langPtr:
      measure "pass:ptr-to-int":
        tree = tree.apply(pass_ptrToInt.lower(tree, PointerSize))
      current = lang0
    of lang1:
      syntaxCheck(tree, lang1_checks, module)
      measure "pass:inline-types":
        tree = tree.apply(pass_inlineTypes.lower(tree))
      current = langPtr
    of lang2:
      syntaxCheck(tree, lang2_checks, module)
      measure "pass:stack-alloc":
        tree = tree.apply(pass_stackAlloc.lower(tree))
      current = lang1
    of lang3:
      syntaxCheck(tree, lang3_checks, module)
      measure "pass:aggregates-to-blob":
        tree = tree.apply(pass_aggregatesToBlob.lower(tree, PointerSize))
      measure "pass:locals-to-blob":
        tree = tree.apply(pass_localsToBlob.lower(tree, PointerSize))
      measure "pass:legalize-blobs":
        tree = tree.apply(pass_legalizeBlobOps.lower(tree))
      current = lang2
    of lang4:
      syntaxCheck(tree, lang4_checks, module)
      measure "pass:lower-aggregate-params":
        tree = tree.apply(pass_aggregateParams.lower(tree))
      current = lang3
    of lang5:
      syntaxCheck(tree, lang5_checks, module)
      measure "pass:flatten-paths":
        tree = tree.apply(pass_flattenPaths.lower(tree))
      current = lang4
    of lang6:
      syntaxCheck(tree, lang6_checks, module)
      measure "pass:globals-to-pointer":
        tree = tree.apply(pass_globalsToPointer.lower(tree, PointerSize))
      current = lang5
    of lang25:
      syntaxCheck(tree, lang25_checks, module)
      measure "pass:basic-blocks":
        tree = tree.apply(pass25.lower(tree))
      current = lang6
    of lang30:
      syntaxCheck(tree, lang30_checks, module)
      measure "pass:goto-rep":
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
      of "measure":
        gMeasure = true
      of "":
        # a `--` means "program arguments follow"
        if cmd != Eval:
          error "providing execution arguments requires eval mode"
        break
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
    module: VmModule
    code: PackedTree[syntax.NodeKind]
    typ: SemType

  if source == langBytecode:
    # run the assembler on the input lines
    var
      a = AssemblerState()
      lineN = 1

    for line in splitLines(text, false):
      try:
        a.process(line)
      except AssemblerError as e:
        error input & "(" & $lineN & ", 1): " & e.msg
      inc lineN

    module = a.close()
  else:
    var newSource = source

    # the input is in some higher-level language
    if source == langSource:
      # translate to the highest-level IL first
      measure "source-to-il":
        (code, typ) = sourceToIL(text)
      newSource = lang30
      print(code, newSource)
    elif gRunner:
      # in order to reduce visual noise in tests, the ``(Module ...)`` top
      # level node is added implicitly
      code = fromSexp[syntax.NodeKind]("(Module " & text & ")")
    else:
      code = fromSexp[syntax.NodeKind](text)

    if target == langBytecode:
      # compile to L0 code and then translate to bytecode
      compile(code, newSource, lang0)
      syntaxCheck(code, lang0)
      measure "vm-gen":
        module = pass0.translate(code)
      # the bytecode is verified later
    else:
      compile(code, newSource, target)
      # make sure the output code is correct:
      syntaxCheck(code, target)

  if gMeasure:
    when declared(EventLog):
      dumpTimings(gEvents)
    else:
      echo "`phy` was not built with instrumentation support"

  if target == langBytecode:
    # make sure the environment is correct:
    let errors = validate(module)
    if errors.len > 0:
      echo "VM module validation failed"
      for it in errors.items:
        echo "Error: ", it
      quit(1)

    print(module)

    # handle the eval command:
    if cmd == Eval:
      var mem: MemoryConfig
      if (let v = readMemConfig(module); v.isSome):
        mem = v.unsafeGet
      else:
        error "invalid memory configuration"

      # setup the VM instance and load all modules (currently only one):
      var env = initVm(mem.initial, mem.maximum)
      var ltab = LinkTable()
      if not load(env, ltab, module):
        error "loading the VM module failed"

      # look for the procedure to start evaluation with:
      var entry = none ProcIndex
      if source == langSource:
        # use the last exported procedure, if any
        for i in countdown(module.exports.high, 0):
          if module.exports[i].kind == expProc:
            entry = some module.exports[i].id.ProcIndex
            break
      elif module.procs.len > 0:
        # simply use the last procedure
        entry = some module.procs.high.ProcIndex

      if entry.isNone:
        if gRunner:
          discard "okay, silently ignore"
          return
        else:
          error "there's nothing to run"

      # import the host procedure's only now, so that the above module-level
      # references are also valid program-level references
      load(env, ltab, hostProcedures(gRunner))
      let stack = hoSlice(mem.stackStart, mem.stackStart + mem.stackSize)

      if source == langSource:
        # we have type high-level type information
        var res: SexpNode
        if gRunner:
          # use an intermediate buffer for the output and error stream
          let stream = newStringStream()
          let cl = HostEnv(outStream: stream, errStream: stream)
          res = run(env, stack, entry.unsafeGet, typ, cl)
          if stream.data.len > 0:
            stdout.write stream.data
            stdout.write "!BREAK!"
        else:
          # write directly to the output and error streams
          let cl = HostEnv(outStream: newFileStream(stdout),
                           errStream: newFileStream(stderr))
          res = run(env, stack, entry.unsafeGet, typ, cl)

        stdout.write $res
        stdout.write " : "
        stdout.write $typeToSexp(typ)
      else:
        # program arguments are only supported for non-source-language
        # programs at the moment
        let cl = HostEnv(params: opts.remainingArgs())

        # we don't have high-level type information
        stdout.write run(env, stack, entry.unsafeGet, cl)

main(getExecArgs())
