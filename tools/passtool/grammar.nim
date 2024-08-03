## Type definitions and associated helper procedures for the grammar IR.

import
  std/[tables, strutils]

type
  Repeat* = enum
    rOnce
    rZeroOrOne
    rZeroOrMore
    rOneOrMore

  SourcePos* = tuple
    file, line, col: uint16

  Rule* = object
    pos*: SourcePos
      ## the source position
    name*: string
      ## an optional name for the rule
    repeat*: Repeat
      ## how many times the expression may repeat
    expr*: Expr

  Expr* = object
    pos*: SourcePos
    name*: string
      ## name of the reference, or symbol of the S-expression
    case isRef*: bool
    of false:
      rules*: seq[Rule]
    of true:
      discard

  Production* = object
    source*: string
      ## name of the language the production comes from
    expr*: Expr

  Grammar* = OrderedTable[string, seq[Production]]

proc `$`*(e: Expr): string

proc `$`*(r: Rule): string =
  if r.name.len > 0:
    result.add r.name
    result.add ":"

  result.add $r.expr
  case r.repeat
  of rOnce:
    discard "nothing to do"
  of rOneOrMore:
    result.add "+"
  of rZeroOrOne:
    result.add "?"
  of rZeroOrMore:
    result.add "*"

proc `$`*(e: Expr): string =
  case e.isRef
  of false:
    result.add '('
    result.add e.name
    for it in e.rules.items:
      result.add ' '
      result.add $it
    result.add ')'
  of true:
    result.add '<'
    result.add e.name
    result.add '>'

proc `$`*(g: Grammar): string =
  for name, it in g.pairs:
    result.add name
    result.add " ::= "
    let offset = name.len + 2
    # format the productions in an easy-to-read way:
    for i, rule in it.pairs:
      if i > 0:
        result.add "\n" & repeat(' ', offset) & "|  "
      result.add $rule.expr
    result.add "\n"
