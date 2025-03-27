## Provides the main data representation for meta-language constructs, plus
## basic operations for operating on the data.

import
  std/tables,
  rationals

type
  NodeKind* = enum
    # leaf nodes:
    nkFail
    nkFalse, nkTrue
    nkNumber
    nkSymbol
    nkString
    nkType
    nkFunc
    nkRelation
    nkContext
    nkVar
    nkHole

    # non-leaf nodes:
    nkConstr, nkTuple
    nkImplies, nkMatches, nkMatch, nkOf
    nkProject, nkCall, nkIf
    nkRecord, nkMap, nkAssoc, nkSet
    nkBind, nkGroup, nkOneOrMore, nkZeroOrMore, nkPlug
    nkUnpack

const
  withChildren* = {
    nkZeroOrMore, nkOneOrMore, nkPlug, nkGroup, nkConstr, nkTuple, nkUnpack,
    nkMap, nkAssoc, nkSet, nkBind, nkRecord, nkCall, nkIf, nkProject,
    nkMatches, nkImplies, nkMatch, nkOf
  }
    ## nodes the have child nodes

type
  Node*[T] = object
    ## Node in an AST representing a meta-language term. Generic so that the
    ## type representation is swappable.
    typ*: T
    case kind*: NodeKind
    of nkType, nkHole, nkTrue, nkFalse, nkFail:
      discard
    of nkNumber:
      num*: Rational
    of nkSymbol, nkString:
      sym*: string
    of nkFunc, nkRelation, nkVar, nkContext:
      id*: int
    of withChildren:
      children*: seq[Node[T]]

  TypeKind* = enum
    tkAll  ## top type
    tkVoid ## bottom type
    tkBool
    tkInt
    tkRat  ## rational number
    tkList
    tkFunc
    tkTuple
    tkRecord ## record type
    tkData   ## inductively defined data type
    tkSum    ## sum type

  TypeId* = int

  Type* = object
    case kind*: TypeKind
    of tkAll, tkVoid, tkBool, tkInt, tkRat:
      discard
    of tkData:
      constr*: seq[Node[TypeId]]
        ## the patterns describing the shapes of valid constructions
    of tkFunc, tkTuple, tkList, tkSum:
      children*: seq[TypeId]
    of tkRecord:
      fields*: seq[tuple[name: string, typ: TypeId]]

  Rule*[T] = object
    ## A rule of an inductively-defined relation.
    name*: string
      ## name of the rule
    body*: Node[T]

  Relation*[T] = object
    ## Describes an inductively-defined boolean relation. It establishes
    ## whether there exists a relation between values.
    name*: string
    params*: seq[tuple[input: bool, typ: T]]
      ## for each parameter whether it's an input or not, plus its type
    rules*: seq[Rule[T]]

  Function*[T] = object
    ## Describes a meta-language function. A function maps one or more input
    ## to an output. It is not required to be *total* (i.e., not all values
    ## part of the domain must have a mapping).
    name*: string
      ## name of the function
    body*: Node[T]

  Pattern*[T] = object
    ## A parameteric and recursive pattern matcher. Usually used for modeling
    ## contextual semantics.
    name*: string
    patterns*: seq[Node[T]]

  LangDef* = object
    ## The full and self-contained description of a language.
    types*: seq[Type]
      ## all meta-language types reference from nodes
    names*: Table[TypeId, string]
      ## names given to types
    functions*: seq[Function[TypeId]]
    relations*: seq[Relation[TypeId]]
    matchers*: seq[Pattern[TypeId]]

template `[]`*(n: Node, i: int|BackwardsIndex): untyped =
  n.children[i]

func len*(n: Node): int =
  n.children.len

func add*[T](n: var Node[T], elem: sink Node[T]) =
  n.children.add elem

template tree*[T](k: NodeKind, c: varargs[Node[T]]): Node[T] =
  Node[T](kind: k, children: @c)

proc tree*[T](k: range[nkConstr..nkUnpack], c: sink seq[Node[T]]): Node[T] =
  Node[T](kind: k, children: c)

proc `[]`*(lang: LangDef, typ: TypeId): lent Type =
  ## Looks up the given `typ`.
  lang.types[typ.ord - 1]
