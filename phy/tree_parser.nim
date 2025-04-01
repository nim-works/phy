## Implements an S-expression to `PackedTree <trees.html#PackedTree>`_ parser.

import
  std/[strutils, streams],
  passes/[trees],
  experimental/[sexp, sexp_parse]

type
  ParseError* = object of ValueError
    ## Error raised by the tree parser when something goes wrong.
    line*, column*: int

proc raiseError(p: SexpParser, msg: sink string) {.noreturn.} =
  raise (ref ParseError)(msg: msg, line: p.getLine(), column: p.getColumn())

template next(p: var SexpParser) =
  discard p.getTok()

proc eat(p: var SexpParser, tok: TTokKind) =
  if p.isTok(tok): p.next()
  else:            p.raiseError("expected " & $tok)

proc fixup(p: var SexpParser): (TTokKind, string) =
  ## The sexp tokenizer tokenizes '-' as an int... This procedure makes sure
  ## the correct token is lexed.
  if p.currToken == tkInt and (p.currString == "-" or p.currString == "+"):
    # could be an identifier or float (like -inf or +inf)
    var str = captureCurrString(p)
    p.next()
    case p.currToken
    of tkSymbol:
      # treat as a float
      str.add p.currString
      (tkFloat, str)
    of tkSpace:
      # treat as a symbol
      (tkSymbol, str)
    else:
      p.raiseError("")
  else:
    (p.currToken, captureCurrString(p))

proc parseLeaf[T](p: var SexpParser, lit: var Literals, kind: T): TreeNode[T] =
  mixin fromSexp
  case p.currToken
  of tkParensRi:
    result = fromSexp(kind)
  of tkInt:
    let (tok, str) = p.fixup()
    if tok == tkFloat:
      result = fromSexp(kind, parseFloat(str), lit)
    else:
      # try to parse as an int otherwise (even if it's not an int)
      result = fromSexp(kind, parseBiggestInt(str), lit)
    p.next()
  of tkFloat, tkSymbol:
    # symbols are also treated as floats (so that "nan" and "inf" are
    # parsed properly)
    result = fromSexp(kind, parseFloat(p.currString), lit)
    p.next()
  of tkString:
    result = fromSexp(kind, captureCurrString(p), lit)
    p.next()
  else:
    p.raiseError("expected ')', int, float, string, or symbol")

  p.space()
  p.eat(tkParensRi)

proc parseSexp*[T](str: string, lit: var Literals): seq[TreeNode[T]] =
  ## Parses a node sequence from `str`, which must be the S-expression
  ## representation of a node tree. A `ParseError <#ParseError>`_ or
  ## ``ValueError`` is raised when an error occurs.
  mixin fromSexp, fromSexpSym, isAtom
  var p: SexpParser
  p.open(newStringStream(str))
  p.next()

  var stack: seq[int]

  template incLen() =
    if stack.len > 0:
      inc result[stack[^1]].val

  # parse tokens until the end-of-stream or end-of-expression is reached
  while true:
    p.space()

    let (tok, str) = p.fixup()
    case tok
    of tkInt:
      incLen()
      result.add fromSexp(T, parseBiggestInt(str), lit)
      p.next()
    of tkFloat:
      incLen()
      result.add fromSexp(T, parseFloat(str), lit)
      p.next()
    of tkString:
      incLen()
      result.add fromSexp(T, str, lit)
      p.next()
    of tkSymbol:
      incLen()
      result.add fromSexpSym(T, str, lit)
      p.next()
    of tkParensLe:
      if p.getTok() != tkSymbol:
        p.raiseError("expected symbol")

      let kind = parseEnum[T](captureCurrString(p))
      p.next()
      p.space()

      incLen()
      if isAtom(kind):
        result.add parseLeaf(p, lit, kind)
      else:
        # start a new sub-tree
        result.add TreeNode[T](kind: kind)
        stack.add result.high

    of tkParensRi:
      p.next()
      if stack.len == 0:
        p.raiseError("unexpected ')'")

      stack.shrink(stack.len - 1) # pop one item
    of tkEof:
      if stack.len > 0:
        p.raiseError("unexpected end")
      break
    of tkError:
      p.raiseError($p.error)
    else:
      p.raiseError("unexpected token: " & $p.currToken)

    if stack.len == 0:
      break

proc fromSexp*[T](str: string): PackedTree[T] =
  ## Parses a tree from `str`, which must be the S-expression representation of
  ## a node tree. A `ParseError <#ParseError>`_ or ``ValueError`` is raised
  ## when an error occurs.
  var literals = Literals()
  result = initTree(parseSexp[T](str, literals), literals)

proc fromSexp[T](n: SexpNode, nodes: var seq[TreeNode[T]], lit: var Literals) =
  mixin isAtom, fromSexp, fromSexpSym
  case n.kind
  of SList:
    assert n.len > 0
    let kind = parseEnum[T](n[0].symbol)
    if isAtom(kind):
      if n.len == 1:
        nodes.add fromSexp(kind)
      else:
        case n[1].kind
        of SInt:    nodes.add fromSexp(kind, n[1].num, lit)
        of SFloat:  nodes.add fromSexp(kind, n[1].fnum, lit)
        of SString: nodes.add fromSexp(kind, n[1].str, lit)
        else:       doAssert false
    else:
      nodes.add TreeNode[T](kind: kind, val: uint32(n.len - 1))
      for i in 1..<n.len:
        fromSexp(n[i], nodes, lit)
  of SInt:
    nodes.add fromSexp(T, n.num, lit)
  of SFloat:
    nodes.add fromSexp(T, n.fnum, lit)
  of SString:
    nodes.add fromSexp(T, n.str, lit)
  of SSymbol:
    nodes.add fromSexpSym(T, n.symbol, lit)
  else:
    doAssert false

proc fromSexp*[T](n: SexpNode): PackedTree[T] =
  ## Parses a tree from `n`, which must be the valid S-expression
  ## representation of a tree.
  var
    literals = Literals()
    nodes    = newSeq[TreeNode[T]]()
  fromSexp(n, nodes, literals)
  result = initTree(nodes, literals)
