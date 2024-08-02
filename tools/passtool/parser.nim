## Implements the lexer and parser for the rule grammar.

import
  std/[lexbase, streams, strformat, strutils]

type
  TokenKind = enum
    tkError
    tkEos # end-of-stream
    tkNewline
    tkSpace
    tkParensLe, tkParensRi
    tkDot
    tkIdent
    tkColon
    tkEq
    tkPlus
    tkMinusEq
    tkQMark
    tkStar
    tkSharpLe, tkSharpRi
    tkSeparator

  Token = object
    line, col: int
    case kind: TokenKind
    of tkIdent, tkError:
      str: string
    else:
      discard

  Lexer* {.final.} = object of BaseLexer
    curr: Token
    currLine, currCol: int

  ParserError = object of ValueError

  RuleKind* = enum
    Reference, SExpr
    Named
    ZeroOrMore, OneOrMore, Optional

  ParsedRule* = object
    line*: int
    col*: int
    kind*: RuleKind
    # for simplicity, don't use a variant object
    sym*: string
    sub*: seq[ParsedRule]

  ParsedKind* = enum
    pkError
    pkImport
    pkDef
    pkAppend
    pkRemove

  Parsed* = object
    ## A parsed item.
    line*: int
    col*: int
    kind*: ParsedKind
    name*: string
    prod*: seq[ParsedRule]

proc seek(L: var Lexer): bool =
  ## Seeks to the start of the next grammar section. Returns true if one was
  ## found, false otherwise.
  const Start = "```grammar"
  while true:
    case L.buf[L.bufpos]
    of '\r':
      L.bufpos = L.handleCR(L.bufpos)
    of '\n':
      L.bufpos = L.handleLF(L.bufpos)
    of '\0':
      return false # end of stream
    of '`':
      if L.bufpos + Start.len <= L.buf.len:
        block compare:
          for i in 1..<Start.len:
            if L.buf[L.bufpos + i] != Start[i]:
              break compare

          inc L.bufpos, Start.len
          return true # found a start

      inc L.bufpos
    else:
      inc L.bufpos

proc open*(L: var Lexer, stream: Stream) =
  open(BaseLexer(L), stream)

proc openWithMarkdown*(L: var Lexer, stream: Stream) =
  ## Opens the lexer with the content of a Markdown file.
  open(L, stream)
  discard seek(L) # seek to the first section

proc close*(L: sink Lexer) =
  close(BaseLexer(L))

proc sequence(L: var Lexer, kind: TokenKind, str: static string): Token =
  if L.bufpos + str.len <= L.buf.len:
    for i in 1..<str.len:
      if L.buf[L.bufpos + i] != str[i]:
        return Token(kind: tkError,
                     str: "unexpected character: " & $L.buf[L.bufpos + i])

    inc L.bufpos, str.len
    result = Token(kind: kind)
  else:
    result = Token(kind: tkError,
                   str: "unexpected character: " & $L.buf[L.bufpos + 1])

proc getTok(L: var Lexer): TokenKind =
  ## Produces the next token from the input stream and updates the current
  ## token of `L`.
  template single(k: TokenKind) =
    inc L.bufpos
    L.curr = Token(kind: k)

  # update the current line/column before consuming the token:
  L.currLine = L.lineNumber
  L.currCol = BaseLexer(L).getColNumber(L.bufpos) + 1

  case L.buf[L.bufpos]
  of ' ', '\t': single(tkSpace)
  of '<': single(tkSharpLe)
  of '>': single(tkSharpRi)
  of '|': single(tkSeparator)
  of '?': single(tkQMark)
  of '*': single(tkStar)
  of '(': single(tkParensLe)
  of ')': single(tkParensRi)
  of '.': single(tkDot)
  of '+': single(tkPlus)
  of '=': single(tkEq)
  of ':': single(tkColon)
  of '-':
    L.curr = sequence(L, tkMinusEq, "-=")
  of '\n':
    L.curr = Token(kind: tkNewline)
    L.bufpos = L.handleLF(L.bufpos)
  of '\r':
    L.curr = Token(kind: tkNewline)
    L.bufpos = L.handleCR(L.bufpos)
  of '#':
    # comments are treated as empty space for simplicity
    inc L.bufpos
    while L.buf[L.bufpos] notin {'\n', '\r', '\0'}:
      inc L.bufpos
    L.curr = Token(kind: tkSpace)
  of 'a'..'z', 'A'..'Z':
    var str = ""
    str.add L.buf[L.bufpos]
    inc L.bufpos
    while L.buf[L.bufpos] in {'a'..'z', 'A'..'Z', '_', '0'..'9'}:
      str.add L.buf[L.bufpos]
      inc L.bufpos
    L.curr = Token(kind: tkIdent, str: str)
  of '\0':
    L.curr = Token(kind: tkEos)
  of '`':
    # must be the end of the markdown code block
    inc L.bufpos
    if L.seek():
      L.curr = Token(kind: tkNewline) # counts as a newline
    else:
      L.curr = Token(kind: tkEos)
  else:
    L.curr = Token(kind: tkError,
                   str: "unexpected character: " & $L.buf[L.bufpos])

  result = L.curr.kind

proc space(L: var Lexer) =
  while L.curr.kind == tkSpace:
    discard L.getTok()

proc error(L: Lexer, expected: TokenKind): ref ParserError =
  ParserError.newException(fmt"expected {expected} but got {L.curr.kind}")

proc consumeIdent(L: var Lexer): string =
  result = move L.curr.str
  discard L.getTok()

proc expect(L: Lexer, kind: TokenKind) =
  ## Expects the current token to be of `kind`, raising an error if that's
  ## not the case.
  if L.curr.kind != kind:
    raise L.error(kind)

proc skip(L: var Lexer, kind: TokenKind) =
  ## Skips the current token if of `kind`; raises an error otherwise.
  L.expect(kind)
  discard L.getTok()

proc expectNext(L: var Lexer, kind: TokenKind) =
  if L.getTok() != kind:
    raise L.error(kind)

proc unexpected(L: Lexer) =
  if L.curr.kind == tkError:
    raise ParserError.newException(L.curr.str)
  else:
    raise ParserError.newException("unexpected token: " & $L.curr.kind)

proc parseRuleCore(L: var Lexer): ParsedRule

proc parseRule(L: var Lexer): ParsedRule =
  result = parseRuleCore(L)
  case L.curr.kind
  of tkPlus:
    discard L.getTok()
    result = ParsedRule(kind: OneOrMore, sub: @[result])
  of tkStar:
    discard L.getTok()
    result = ParsedRule(kind: ZeroOrMore, sub: @[result])
  of tkQMark:
    discard L.getTok()
    result = ParsedRule(kind: Optional, sub: @[result])
  else:
    discard "okay, not part of the rule"

proc parseRuleCore(L: var Lexer): ParsedRule =
  result = ParsedRule(line: L.currLine, col: L.currCol)
  case L.curr.kind
  of tkSharpLe:
    L.expectNext(tkIdent)
    result.kind = Reference
    result.sym = toLowerAscii L.consumeIdent()
    L.skip(tkSharpRi)
  of tkParensLe:
    discard L.getTok()
    L.space()
    L.expect(tkIdent)
    result.kind = SExpr
    result.sym = L.consumeIdent()
    L.space()
    while L.curr.kind notin {tkParensRi, tkEos}:
      result.sub.add parseRule(L)
      L.space()
    L.skip(tkParensRi)
  of tkIdent:
    result.kind = Named
    result.sym = L.consumeIdent()
    L.skip(tkColon)
    result.sub.add parseRule(L)
  else:
    L.unexpected()

proc makeParsed(L: Lexer, kind: ParsedKind, name: sink string): Parsed =
  Parsed(line: L.currLine, col: L.currCol, kind: kind, name: name)

proc parseNamedRule(L: var Lexer): Parsed =
  L.space()
  L.expect(tkIdent)
  result = L.makeParsed(pkDef, toLowerAscii L.consumeIdent())
  L.space()
  case L.curr.kind
  of tkColon:
    L.expectNext(tkColon)
    L.expectNext(tkEq)
    result.kind = pkDef
  of tkPlus:
    L.expectNext(tkEq)
    result.kind = pkAppend
  of tkMinusEq:
    result.kind = pkRemove
  else:
    L.unexpected()

  discard L.getTok()

  L.space()
  while true:
    result.prod.add parseRuleCore(L)
    L.space()
    # skip newlines. If there's a space following the newline, the next
    # line is treated as a continuation of the current one
    if L.curr.kind in {tkNewline, tkEos} and L.getTok() != tkSpace:
      break

    L.space()
    L.skip(tkSeparator)
    L.space()

proc parseDirective(L: var Lexer): Parsed =
  ## Parses a directive.
  L.skip(tkDot)
  L.expect(tkIdent)
  # detect the directive in the parser already; it's simpler
  let dir = L.consumeIdent()
  case dir
  of "extends":
    L.space()
    L.makeParsed(pkImport, L.consumeIdent())
  else:
    L.makeParsed(pkError, "unknown directive: " & dir)

proc parseTopLevel(L: var Lexer): Parsed =
  ## Parses a top-level item.
  case L.curr.kind
  of tkDot:
    try:
      L.parseDirective()
    except ParserError as e:
      L.makeParsed(pkError, e.msg)
  of tkIdent:
    try:
      L.parseNamedRule()
    except ParserError as e:
      L.makeParsed(pkError, e.msg)
  of tkError:
    L.makeParsed(pkError, L.curr.str)
  else:
    L.makeParsed(pkError, "unexpected token: " & $L.curr.kind)

iterator parse*(L: var Lexer): Parsed =
  ## Produces and parses the tokens from `L` until an error is encounted or
  ## the end of stream is reached. The parsed items are returned.
  discard L.getTok()
  # skip empty space:
  while L.curr.kind in {tkNewline, tkSpace}:
    discard L.getTok()

  var stop = false
  while L.curr.kind != tkEos and not stop:
    L.space()
    let parsed = parseTopLevel(L)
    # stop after an error:
    stop = parsed.kind == pkError
    yield parsed

    # skip empty space:
    while L.curr.kind in {tkNewline, tkSpace}:
      discard L.getTok()
