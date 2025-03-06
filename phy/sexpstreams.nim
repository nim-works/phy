## Implements a stream that reads lines from `stdin`, plus a closure iterator
## for parsing `SexprNode`s from a stream.

import
  std/[
    streams,
    strutils
  ],
  experimental/[
    sexp,
    sexp_parse
  ]

type
  LineBufferedStream = ref object of Stream
    ## A stream implementation that returns lines from the standard input.
    line: string
    pos: int

iterator parse*(stream: Stream): tuple[n: SexpNode, depth: int] {.closure.} =
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

proc newLineBufferedStream*(): LineBufferedStream =
  ## Creates a new line-buffered stream.
  LineBufferedStream(readDataStrImpl: readDataStrImpl)
