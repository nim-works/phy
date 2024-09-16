## Implements a REPL (read-eval-print loop) program for the source language.

import
  std/[
    streams,
    strutils
  ],
  experimental/[
    sexp,
    sexp_parse
  ],
  passes/[
    changesets,
    pass0,
    pass1,
    pass3,
    pass4,
    pass10,
    source2il,
    spec_source,
    trees,
  ],
  phy/[
    types
  ],
  common/[
    vmexec
  ],
  vm/[
    vmenv,
    vmvalidation
  ]

type
  LineBufferedStream = ref object of Stream
    ## A stream implementation that returns lines from the standard input.
    line: string
    pos: int

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

proc process(ctx: var ModuleCtx, tree: PackedTree[NodeKind]) =
  case tree[NodeIndex(0)].kind
  of DeclNodes:
    if ctx.declToIL(tree, NodeIndex(0)).kind == TypeKind.tkError:
      echo "error in declaration"

  of ExprNodes:
    let typ = ctx.exprToIL(tree)

    # don't continue if there was an error:
    if typ.kind == TypeKind.tkError:
      echo "expression has an error"
      return

    # XXX: rather inefficient. Ideally, only the new code would be
    #      compiled
    var m = close(ctx)

    # lower to L0:
    m = m.apply(pass10.lower(m))
    m = m.apply(pass4.lower(m))
    m = m.apply(pass3.lower(m, 8))
    m = m.apply(pass1.lower(m, 8))

    # generate the bytecode:
    var env = initVm(1024, 1024 * 1024)
    translate(m, env)

    # make sure the bytecode and environment is correct:
    let errors = validate(env)
    if errors.len > 0:
      for it in errors.items:
        echo it
      echo "validation failure"
      return

    # eval and print:
    echo run(env, ProcIndex(env.procs.high), typ)
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
var module = source2il.open()

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

      process(module):
        try:
          fromSexp[NodeKind](n)
        except ValueError as e:
          # don't crash the REPL on incorrect syntax
          echo "Error: ", e.msg
          continue
