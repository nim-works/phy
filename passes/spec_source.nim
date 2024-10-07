## Provides the type definitions for the source languages.

# XXX: this module is going be auto-generated by the passtool in the future

import
  experimental/sexp,
  passes/trees,
  vm/utils

type
  NodeKind* {.pure.} = enum
    Immediate, IntVal, FloatVal
    Ident,
    VoidTy, UnitTy, BoolTy, IntTy, FloatTy, TupleTy, UnionTy
    Call
    TupleCons
    FieldAccess
    Exprs
    Asgn
    Return
    Unreachable
    Params
    ProcDecl
    Decl
    TypeDecl
    Module

const
  ExprNodes* = {IntVal, FloatVal, Ident, Call, TupleCons, FieldAccess, Asgn, Return,
                Unreachable, Exprs, Decl}
  DeclNodes* = {ProcDecl, TypeDecl}
  AllNodes* = {low(NodeKind) .. high(NodeKind)}

template isAtom*(x: NodeKind): bool =
  ord(x) <= ord(Ident)

proc fromSexp*(tree: var PackedTree[NodeKind], kind: NodeKind,
               n: SexpNode): TreeNode[NodeKind] =
  case kind
  of IntVal:
    TreeNode[NodeKind](kind: kind, val: tree.pack(n[1].num))
  of FloatVal:
    TreeNode[NodeKind](kind: FloatVal, val: tree.pack(n[1].fnum))
  of Ident:
    TreeNode[NodeKind](kind: Ident, val: tree.pack(n[1].str))
  else:
    unreachable()

proc toSexp*(tree: PackedTree[NodeKind], idx: NodeIndex,
             n: TreeNode[NodeKind]): SexpNode =
  case n.kind
  of Immediate: sexp(n.val.int)
  of IntVal:    sexp([newSSymbol("IntVal"), sexp tree.getInt(idx)])
  of FloatVal:  sexp([newSSymbol("FloatVal"), sexp tree.getFloat(idx)])
  of Ident:     sexp([newSSymbol("Ident"), sexp tree.getString(idx)])
  else:         unreachable()

proc fromSexp*(i: BiggestInt): TreeNode[NodeKind] =
  TreeNode[NodeKind](kind: Immediate, val: i.uint32)
