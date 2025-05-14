## Implements a REPL (read-eval-print loop) program for the source language.

import
  std/[
    options,
    streams,
    strutils
  ],
  experimental/[
    colortext,
    sexp
  ],
  generated/[
    source_checks
  ],
  passes/[
    changesets,
    pass0,
    pass_aggregateParams,
    pass_aggregatesToBlob,
    pass_globalsToPointer,
    pass_legalizeBlobOps,
    pass_inlineTypes,
    pass_stackAlloc,
    pass_localsToBlob,
    pass_flattenPaths,
    pass25,
    pass30,
    source2il,
    syntax_source,
    trees,
  ],
  phy/[
    sexpstreams,
    default_reporting,
    host_impl,
    tree_parser,
    vmexec
  ],
  vm/[
    utils,
    vmenv,
    vmmodules,
    vmvalidation
  ]

type
  Reporter = ref DefaultReporter[string]

proc process(ctx: var ModuleCtx, reporter: Reporter,
             tree: PackedTree[NodeKind]) =
  case tree[NodeIndex(0)].kind
  of DeclNodes:
    source_checks.check tree, NodeIndex(0), decl:
      echo "Syntax error: \"", rule, "\" didn't match"
      return

    ctx.declToIL(tree, NodeIndex(0))

    for msg in reporter[].retrieve().items:
      echo "Error: " + fgRed, msg

  of ExprNodes:
    source_checks.check tree, NodeIndex(0), expr:
      echo "Syntax error: \"", rule, "\" didn't match"
      return

    let typ = ctx.exprToIL(tree)
    let entry = ctx.entry

    let messages = reporter[].retrieve()
    for msg in messages.items:
      echo "Error: " + fgRed, msg

    # don't continue if there was an error:
    if messages.len > 0:
      return

    # XXX: rather inefficient. Ideally, only the new code would be
    #      compiled
    var m = close(ctx)

    # lower to L0:
    m = m.apply(pass30.lower(m))
    m = m.apply(pass25.lower(m))
    m = m.apply(pass_globalsToPointer.lower(m, 8))
    m = m.apply(pass_flattenPaths.lower(m))
    m = m.apply(pass_aggregateParams.lower(m))
    m = m.apply(pass_aggregatesToBlob.lower(m, 8))
    m = m.apply(pass_localsToBlob.lower(m, 8))
    m = m.apply(pass_legalizeBlobOps.lower(m))
    m = m.apply(pass_stackAlloc.lower(m))
    m = m.apply(pass_inlineTypes.lower(m))

    let module = translate(m)

    # make sure the module is correct:
    let errors = validate(module)
    if errors.len > 0:
      for it in errors.items:
        echo it
      echo "validation failure"
      return

    var mem: MemoryConfig
    if (let v = readMemConfig(module); v.isSome):
      mem = v.unsafeGet
    else:
      unreachable("memory config invalid; there's probably a bug in source2il")

    var env = initVm(mem.initial, mem.maximum)
    var ltab = LinkTable()
    if not load(env, ltab, module):
      echo "Error: couldn't load module"
      return
    load(env, ltab, hostProcedures(includeTest = false))

    let cl = HostEnv(outStream: newFileStream(stdout),
                     errStream: newFileStream(stderr))
    # eval and print:
    echo run(env, hoSlice(mem.stackStart, mem.stackStart + mem.stackSize),
             ProcIndex(entry), typ, cl)
  else:
    echo "Error: unexpected node: ", tree[NodeIndex(0)].kind

var stream = newLineBufferedStream()
var depth = 0 ## the current S-expression nesting
var iter = parse
var reporter = initDefaultReporter[string]()
var module = source2il.open(reporter)

block loop:
  while not finished(iter):
    if depth > 0:
      stdout.write "... "
      for it in 0..<depth:
        stdout.write "  "
    else:
      stdout.write ">>> "
    stdout.flushFile()

    # parse everything until the first line break is reached:
    while (var n: SexpNode; (n, depth) = iter(stream); n != nil):
      # a ``(quit)`` terminates the REPL
      if n.len == 1 and n[0].kind == SSymbol and n[0].symbol == "quit":
        break loop # quit

      process(module, reporter):
        try:
          fromSexp[NodeKind](n)
        except ValueError as e:
          # don't crash the REPL on incorrect syntax
          echo "Error: ", e.msg
          continue
