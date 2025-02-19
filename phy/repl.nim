## Implements a REPL (read-eval-print loop) program for the source language.

import
  std/[
    options,
    streams,
    strutils
  ],
  experimental/[
    colortext,
    sexp,
    sexp_parse
  ],
  generated/[
    source_checks
  ],
  passes/[
    changesets,
    pass0,
    pass_aggregateParams,
    pass_aggregatesToBlob,
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
  LineBufferedStream = ref object of Stream
    ## A stream implementation that returns lines from the standard input.
    line: string
    pos: int

  Reporter = ref DefaultReporter[string]

iterator parse(stream: Stream): tuple[n: SexpNode, depth: int] {.closure.} =
  ## Incrementally parses an S-expression from `stream`. The iterator yields:
  ## * an S-expression, once a full one is complete
  ## * the current nesting depth, when a dot is encountered
  ##
  ## On EOF, the iterator finishes.
  var
    p: SexpParser
    stack: seq[SexpNode]

  p.open(stream)

  while true:
    discard p.getTok() # fetch the next token
    p.space()
    case p.currToken
    of tkString:
      stack[^1].add sexp(captureCurrString(p))
    of TTokKind.tkInt:
      stack[^1].add sexp(parseBiggestInt(p.currString))
    of TTokKind.tkFloat:
      stack[^1].add sexp(parseFloat(p.currString))
    of tkSymbol:
      stack[^1].add newSSymbol(p.currString)
    of tkParensLe:
      stack.add newSList()
    of tkParensRi:
      case stack.len
      of 0:
        raiseParseErr(p, "unexpected token: " & $p.currToken)
      of 1:
        yield (stack.pop(), 0) # a complete S-expression
      else:
        let n = stack.pop()
        # append to the parent
        stack[^1].add n

    of TTokKind.tkError:
      raiseParseErr(p, $p.error)
    of tkSpace, tkNil, tkKeyword:
      raiseParseErr(p, "unexpected token: " & $p.currToken)
    of tkDot:
      # the dot is used to indicate that a user interaction is required
      yield (nil, stack.len)
    of tkEof:
      if stack.len > 0:
        raiseParseErr(p, "unexpected end-of-file")
      # we're done
      return (nil, 0)

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
    m = m.apply(pass_flattenPaths.lower(m))
    m = m.apply(pass_aggregateParams.lower(m, 8))
    m = m.apply(pass_aggregatesToBlob.lower(m, 8))
    m = m.apply(pass_localsToBlob.lower(m))
    m = m.apply(pass_legalizeBlobOps.lower(m))
    m = m.apply(pass_stackAlloc.lower(m, 8))
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

    var env = initVm(mem.total, mem.total)
    link(env, hostProcedures(includeTest = false), [module])

    let cl = HostEnv(outStream: newFileStream(stdout),
                     errStream: newFileStream(stderr))
    # eval and print:
    echo run(env, hoSlice(mem.stackStart, mem.stackStart + mem.stackSize),
             ProcIndex(entry), typ, cl)
  else:
    echo "Error: unexpected node: ", tree[NodeIndex(0)].kind

proc readDataStrImpl(s: Stream, buffer: var string, slice: Slice[int]): int =
  ## Implements the ``readStrData`` procedure for ``LineBufferedStream``.
  ## This is aimed specifically at being used in conjunction with
  ## ``SexpParser``.
  if slice.len == 0:
    return 0 # do nothing

  let s = LineBufferedStream(s)
  if s.line.len == s.pos:
    # fetch the next line and block if none is available
    s.line = stdin.readLine()
    s.pos = 0

  let len = min(s.line.len, slice.len)
  if len > 0:
    copyMem(addr buffer[0], addr s.line[s.pos], len)
    s.pos += len

  # pad rest with spaces:
  let start = slice.a + len
  for i in start..(slice.b-2):
    buffer[i] = ' '

  # mark the end of the currently available line data with a dot:
  if slice.b - start >= 1:
    if slice.b - start >= 2:
      buffer[slice.b - 1] = '.'
      buffer[slice.b - 0] = '\n'
    else:
      buffer[slice.b] = '.'

  result = slice.len

# setup the stream:
var stream = LineBufferedStream()
stream.readDataStrImpl = readDataStrImpl

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
