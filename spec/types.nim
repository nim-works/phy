## Provides the main data representation for language definitions, plus basic
## operations for operating on the data.

type
  NodeKind* = enum
    # leaf nodes:
    nkSymbol
    nkNumber
    nkNonTerminal
    nkHole
    nkAny
    nkAnyInt
    nkAnyRational
    nkAnySymbol
    nkVar

    # non-leaf nodes:
    nkList, nkTree
    nkMap, nkMapEntry, nkSet
    nkNot, nkBind, nkGroup, nkOneOrMore, nkZeroOrMore, nkPlug, nkChoice
    nkUnpack

  TreeNode* = object
    ## Node in an AST representing a meta-language term or pattern. Patterns
    ## and terms have a large amount of overlap (most terms are also valid
    ## patterns), so they share the same node type for convenience.
    case kind*: NodeKind
    of nkSymbol, nkNumber:
      sym*: string
    of nkNonTerminal, nkVar:
      id*: int
    of nkZeroOrMore, nkOneOrMore, nkPlug, nkGroup, nkList, nkTree, nkChoice,
       nkUnpack, nkNot, nkMap, nkMapEntry, nkSet, nkBind:
      children*: seq[TreeNode]
    of nkHole, nkAny, nkAnyInt, nkAnyRational, nkAnySymbol:
      discard

  ExprNodeKind* = enum
    ekIdent
    ekVar
    ekFunc
    ekLookup
    ekTerm
    ekApp
    ekGroup
    ekUnpack

  ExprNode* = object
    ## Node in an AST representing an expression.
    case kind*: ExprNodeKind
    of ekIdent:
      ident*: string
    of ekVar, ekFunc:
      id*: int
    of ekLookup, ekApp, ekGroup, ekUnpack:
      children*: seq[ExprNode]
    of ekTerm:
      term*: TreeNode

  NonTerminal* = object
    ## A named pattern.
    name*: string
    empty*: bool
    pattern*: TreeNode

  Premise* = object
    ## Represents a premise of a function invocation or induction rule.
    repeat*: bool
      ## whether the premise is repeated
    rel*: int
      ## ID of the applied relation/judgment
    inputs*: seq[TreeNode]
    outputs*: seq[TreeNode]

  PredicateKind* = enum
    pkPremise       # a relation must exist
    pkWhere         # a term must match a pattern (variables are bound)
    pkSideCondition # an expression must evaluate to true

  Predicate* = object
    ## Describes a rule or function predicate.
    case kind*: PredicateKind
    of pkPremise:
      premise*: Premise
    of pkWhere:
      pat*: TreeNode
      term*: ExprNode
    of pkSideCondition:
      expr*: ExprNode

  Rule* = object
    ## A rule of an inductively-defined relation.
    name*: string
      ## name of the rule
    predicates*: seq[Predicate]
    conclusion*: seq[TreeNode]

  Relation* = object
    ## Describes an inductively-defined boolean relation. It establishes
    ## whether there exists a relation between terms.
    name*: string
    params*: seq[bool]
      ## for each parameter whether it's an input or not
    format*: string
      ## a formatting pattern specifying how the relation is rendered
    rules*: seq[Rule]

  FunctionImpl* = object
    ## An association of parameters with a result.
    params*: seq[TreeNode]
    predicates*: seq[Predicate]
    output*: ExprNode

  Function* = object
    ## Describes a meta-language function. A function maps one ore more input
    ## terms to an output term. It is not required to be *total* (i.e., not all
    ## terms matching the parameter pattern need to map to an output).
    name*: string
      ## name of the function
    params*: seq[TreeNode]
    impls*: seq[FunctionImpl]

  Language* = object
    ## The full and self-contained description of a language.
    nterminals*: seq[NonTerminal]
    functions*: seq[Function]
    relations*: seq[Relation]

const
  PatternNodes* = {nkAny, nkBind, nkChoice, nkGroup, nkAnyInt, nkAnyRational,
                   nkAnySymbol, nkNonTerminal, nkHole}
    ## nodes that may only appear in patterns

  TermNode* = {nkNumber, nkSymbol, nkTree, nkList}
    ## nodes that may only appear in terms

  MetaNodes* = {nkUnpack}
    ## nodes that are processed before anything else

template `[]`*(n: TreeNode, i: int): lent TreeNode =
  n.children[i]

template node*(k: NodeKind, sub: TreeNode): TreeNode =
  TreeNode(kind: k, children: @[sub])

template exprNode*(k: ExprNodeKind, sub: ExprNode): ExprNode =
  ExprNode(kind: k, children: @[sub])

func add*(n: var TreeNode, elem: sink TreeNode) =
  n.children.add elem

func add*(n: var ExprNode, elem: sink ExprNode) =
  n.children.add elem
