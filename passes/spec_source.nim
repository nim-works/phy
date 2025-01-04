## Provides the type definitions for the source languages.

# XXX: this module is going be auto-generated by the passtool in the future

import
  experimental/sexp,
  passes/trees,
  vm/utils

type
  NodeKind* {.pure.} = enum
    IntVal, FloatVal
    Ident,
    VoidTy, UnitTy, BoolTy, IntTy, FloatTy, TupleTy, UnionTy, ProcTy, SeqTy
    And, Or
    If
    While
    Call
    TupleCons
    Seq
    FieldAccess, At
    Exprs
    Asgn
    Return
    Unreachable
    Params
    ProcDecl, ParamDecl
    Decl
    TypeDecl
    Module

  Node = TreeNode[NodeKind]

const
  ExprNodes* = {IntVal, FloatVal, Ident, And, Or, If, While, Call, TupleCons,
                Seq, FieldAccess, At, Asgn, Return, Unreachable, Exprs, Decl}
  DeclNodes* = {ProcDecl, TypeDecl}
  AllNodes* = {low(NodeKind) .. high(NodeKind)}

using
  lit: var Literals

template isAtom*(x: NodeKind): bool =
  ord(x) <= ord(Ident)

proc toSexp*(tree: PackedTree[NodeKind], idx: NodeIndex,
             n: TreeNode[NodeKind]): SexpNode =
  case n.kind
  of IntVal:    sexp([newSSymbol("IntVal"), sexp tree.getInt(idx)])
  of FloatVal:  sexp([newSSymbol("FloatVal"), sexp tree.getFloat(idx)])
  of Ident:     sexp([newSSymbol("Ident"), sexp tree.getString(idx)])
  else:         unreachable()

proc fromSexp*(kind: NodeKind): Node =
  raise ValueError.newException($kind & " node is missing operand")

proc fromSexp*(kind: NodeKind, val: BiggestInt, lit): Node =
  assert kind == IntVal
  Node(kind: kind, val: lit.pack(val))

proc fromSexp*(kind: NodeKind, val: BiggestFloat, lit): Node =
  assert kind == FloatVal
  Node(kind: kind, val: lit.pack(val))

proc fromSexp*(kind: NodeKind, val: string, lit): Node =
  assert kind == Ident
  Node(kind: kind, val: lit.pack(val))

proc fromSexp*(_: typedesc[NodeKind], val: BiggestInt, lit): Node =
  Node(kind: IntVal, val: lit.pack(val))

proc fromSexp*(_: typedesc[NodeKind], val: BiggestFloat, lit): Node =
  Node(kind: FloatVal, val: lit.pack(val))

proc fromSexp*(_: typedesc[NodeKind], val: string, lit): Node =
  raise ValueError.newException("standalone strings are not supported")

proc fromSexpSym*(_: typedesc[NodeKind], val: string, lit): Node =
  Node(kind: Ident, val: lit.pack(val))
