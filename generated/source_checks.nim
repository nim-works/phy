# Generated by the passtool; do not modify
import passes/trees
import passes/spec_source

type
  Tree = PackedTree[NodeKind]
  Error = object
    pos: NodeIndex
    rule: string
    node: NodeIndex
    child: int

template setError(e, n: NodeIndex; c: int; r: string) =
  if ord(err.pos) < ord(e):
    err = Error(pos: e, rule: r, node: n, child: c)

proc matchAtom(tree: Tree; n: var NodeIndex; kind: NodeKind): bool =
  result = n in tree and tree[n].kind == kind
  if result:
    n = tree.next(n)

template matchTree(rule: string; k: NodeKind; label, body: untyped) =
  when isAtom(k):
    result = matchAtom(tree, n, k)
  else:
    if n in tree and tree[n].kind == k:
      let save = n
      let len {.inject.} = tree.len(n)
      var num {.inject.} = 0
      var success = false
      n = tree.child(n, 0)
      block label:
        body
        success = num == len
      result = success
      if not result:
        setError n, save, num, rule
        n = save

proc check_ident*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_expr*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_type_expr*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_decl*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_module*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_top*(tree: Tree, n: var NodeIndex, err: var Error): bool

proc check_ident*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Ident <string>)", Ident, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true

proc check_expr*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  if check_ident(tree, n, err): return true
  matchTree "(IntVal <int>)", IntVal, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true
  matchTree "(FloatVal <float>)", FloatVal, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true
  matchTree "(Return <expr>?)", Return, match:
    if num < len and check_expr(tree, n, err): inc num
  if result: return true
  matchTree "(Unreachable)", Unreachable, match:
    discard
  if result: return true
  matchTree "(Call <ident> <expr>*)", Call, match:
    if num == len or not check_ident(tree, n, err): break match
    inc num
    while num < len:
      if not check_expr(tree, n, err): break
      inc num
  if result: return true
  matchTree "(TupleCons)", TupleCons, match:
    discard
  if result: return true
  matchTree "(TupleCons <expr>+)", TupleCons, match:
    var tmp = num
    while num < len:
      if not check_expr(tree, n, err): break
      inc num
    if tmp == num: break match
  if result: return true

proc check_type_expr*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(VoidTy)", VoidTy, match:
    discard
  if result: return true
  matchTree "(UnitTy)", UnitTy, match:
    discard
  if result: return true
  matchTree "(BoolTy)", BoolTy, match:
    discard
  if result: return true
  matchTree "(IntTy)", IntTy, match:
    discard
  if result: return true
  matchTree "(FloatTy)", FloatTy, match:
    discard
  if result: return true
  matchTree "(TupleTy)", TupleTy, match:
    discard
  if result: return true
  matchTree "(TupleTy <type_expr>+)", TupleTy, match:
    var tmp = num
    while num < len:
      if not check_type_expr(tree, n, err): break
      inc num
    if tmp == num: break match
  if result: return true

proc check_decl*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(ProcDecl <ident> <type_expr> (Params) <expr>)", ProcDecl, match:
    if num == len or not check_ident(tree, n, err): break match
    inc num
    if num == len or not check_type_expr(tree, n, err): break match
    inc num
    matchTree "(Params)", Params, match:
      discard
    if num == len or not result: break match
    inc num
    if num == len or not check_expr(tree, n, err): break match
    inc num
  if result: return true

proc check_module*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Module <decl>*)", Module, match:
    while num < len:
      if not check_decl(tree, n, err): break
      inc num
  if result: return true

proc check_top*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  if check_module(tree, n, err): return true


template check*(tree: Tree; n: NodeIndex; name, onErr: untyped) =
  if true:
    var
      error: Error
      node = n
    if not `check name`(tree, node, error):
      let
        rule {.inject, used.} = error.rule
        node {.inject, used.} = error.node
        child {.inject, used.} = error.child
      onErr
