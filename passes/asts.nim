## Implements a generic packed storage type for arbitrary abstract syntax
## trees -- no restrictions regarding the grammar are made.

import
  passes/[literals, trees],
  experimental/sexp

type
  AstNode*[T] = object
    ## A single node. How the `val` field is interpreted depends on the kind.
    ## For leaf nodes, the field's meaning is decided externally, while for
    ## non-leaf nodes, `val` stores the number of child nodes the node has.
    kind*: T
    val*: uint32

  Ast*[T] = object
    ## A self contained abstract-syntax-tree (=AST).
    nodes*: PackedTree[AstNode[T]]
    literals: Literals

export trees.NodeIndex

proc initAst*[T](nodes: sink PackedTree[AstNode[T]],
                 literals: sink Literals): Ast[T] =
  Ast[T](nodes: nodes, literals: literals)

proc getInt*(tree: Ast, n: NodeIndex): int64 =
  ## Returns the number stored by `n` as a signed integer.
  tree.literals.loadInt(tree[n].val)

proc getUInt*(tree: Ast, n: NodeIndex): uint64 =
  ## Returns the number stored by `n` as an unsigned integer.
  tree.literals.loadUInt(tree[n].val)

proc getFloat*(tree: Ast, n: NodeIndex): float64 =
  ## Returns the number stored by `n` as a float.
  tree.literals.loadFloat(tree[n].val)

proc getString*(tree: Ast, n: NodeIndex): lent string =
  ## Returns the string value stored by `n`.
  tree.literals.loadString(tree[n].val)

func literals*(tree: Ast): lent Literals {.inline.} =
  ## Returns the storage for the literal data.
  tree.literals

proc pack*(tree: var Ast, i: int64): uint32 {.inline.} =
  ## Packs `i` into a ``uint32`` value that can be stored in a ``AstNode``.
  pack(tree.literals, i)

proc pack*(tree: var Ast, f: float64): uint32 {.inline.} =
  ## Packs `f` into a ``uint32`` value that can be stored in a ``AstNode``.
  pack(tree.literals, f)

proc pack*(tree: var Ast, s: sink string): uint32 {.inline.} =
  ## Packs `s` into a ``uint32`` value that can be stored in a ``AstNode``.
  pack(tree.literals, s)

template newNode*[T](k: T): AstNode[T] =
  ## Creates an AST node with kind `k`.
  AstNode[T](kind: k)

template newNode*[T](k: T, v: uint32): AstNode[T] =
  ## Creates an AST node with kind `k` and raw value `v`.
  AstNode[T](kind: k, val: v)

# TODO: move the S-expression serialization/deserialization elsewhere

proc toSexp*[T](tree: PackedTree[T], at: NodeIndex): SexpNode =
  mixin isAtom, toSexp
  if isAtom(tree[at].kind):
    result = toSexp(tree, at, tree[at])
  else:
    result = newSList()
    result.add newSSymbol($tree[at].kind)
    for it in tree.items(at):
      result.add toSexp(tree, it)

# ------ wrappers for tree operations --------
# below are forwarding adapeters for all `PackedTree` operations, so that an
# `Ast` can be used the same way a tree is

template `[]`*[T](ast: Ast[T], n: NodeIndex): AstNode[T] =
  `[]`(ast.nodes, n)

template contains*(ast: Ast, n: NodeIndex): bool =
  contains(ast.nodes, n)

template next*(ast: Ast, n: NodeIndex): NodeIndex =
  next(ast.nodes, n)

template first*(ast: Ast, n: NodeIndex): NodeIndex =
  first(ast.nodes, n)

template child*(ast: Ast, n: NodeIndex, c: Natural): NodeIndex =
  child(ast.nodes, n, c)

template child*(ast: Ast, i: NodeIndex, c: BackwardsIndex): NodeIndex =
  child(ast.nodes, i, c)

template child*(ast: Ast, i: Natural): NodeIndex =
  child(ast.nodes, i)

template `[]`*[T](ast: Ast[T], i: NodeIndex, c: Natural): AstNode[T] =
  `[]`(ast.nodes, i, c)

template len*(ast: Ast, i: NodeIndex): int =
  len(ast.nodes, i)

template last*(ast: Ast, n: NodeIndex): NodeIndex =
  last(ast.nodes, n)

template fin*(ast: Ast, n: NodeIndex): NodeIndex =
  fin(ast.nodes, n)

iterator items*(ast: Ast, at: NodeIndex): NodeIndex =
  for it in items(ast.nodes, at):
    yield it

iterator items*(ast: Ast, at: NodeIndex; start: int; last = ^1): NodeIndex =
  for it in items(ast.nodes, at, start, last):
    yield it

iterator pairs*(ast: Ast, at: NodeIndex): (int, NodeIndex) =
  for it in pairs(ast.nodes, at):
    yield it

iterator flat*(ast: Ast, at: NodeIndex): NodeIndex =
  for it in flat(ast.nodes, at):
    yield it

iterator filter*[T](ast: Ast[T], at: NodeIndex,
                    filter: static set[T]): NodeIndex =
  for it in filter(ast.nodes, at, filter):
    yield it

template pair*(ast: Ast, n: NodeIndex): (NodeIndex, NodeIndex) =
  pair(ast.nodes, n)

template triplet*(ast: Ast, n: NodeIndex): (NodeIndex, NodeIndex, NodeIndex) =
  triplet(ast.nodes, n)
