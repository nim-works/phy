## Provides the type definitions for the various intermediate languages.

# XXX: this module is going be auto-generated by the (not yet implemented)
#      language grammar management tool

import
  experimental/sexp,
  passes/trees,
  vm/utils

type
  NodeKind* = enum
    Immediate, IntVal, FloatVal, ProcVal, Proc, Type, Local, Global

    List

    Void, Int, UInt, Float, ProcTy, Blob, Record, Array

    Copy, Asgn, Drop, Clear

    Load, Store, Addr, Call
    Deref, Field, At
    Move, Rename

    Neg, Add, Sub, Mul, Div, Mod
    AddChck, SubChck

    Not, Eq, Le, Lt
    BitAnd, BitNot, BitXor, BitOr
    Shl, Shr

    Conv, Reinterp

    Continue, Loop, Raise, Unreachable, Select, SelectBool
    CheckedCall, CheckedCallAsgn, Unwind, Choice

    Module, TypeDefs, ProcDefs, ProcDef, Locals, Continuations, Continuation,
    Except, Params, GlobalDefs, GlobalDef

    Break, Return, Case, If, Block, Stmts

template isAtom*(x: NodeKind): bool =
  ord(x) <= ord(Global)

proc fromSexp*(tree: var PackedTree[NodeKind], kind: NodeKind,
               n: SexpNode): TreeNode[NodeKind] =
  case kind
  of IntVal:
    TreeNode[NodeKind](kind: kind, val: tree.pack(n[1].num))
  of FloatVal:
    TreeNode[NodeKind](kind: FloatVal, val: tree.pack(n[1].fnum))
  of ProcVal, Proc, Type, Local, Global:
    TreeNode[NodeKind](kind: kind, val: n[1].num.uint32)
  else:
    unreachable()

proc toSexp*(tree: PackedTree[NodeKind], idx: NodeIndex,
             n: TreeNode[NodeKind]): SexpNode =
  case n.kind
  of Immediate: sexp(n.val.int)
  of IntVal:    sexp([newSSymbol("IntVal"), sexp tree.getInt(idx)])
  of FloatVal:  sexp([newSSymbol("FloatVal"), sexp tree.getFloat(idx)])
  of ProcVal:   sexp([newSSymbol("ProcVal"), sexp n.val.int])
  of Proc:      sexp([newSSymbol("Proc"), sexp n.val.int])
  of Type:      sexp([newSSymbol("Type"), sexp n.val.int])
  of Local:     sexp([newSSymbol("Local"), sexp n.val.int])
  of Global:    sexp([newSSymbol("Global"), sexp n.val.int])
  else:         unreachable()

proc fromSexp*(i: BiggestInt, _: typedesc[NodeKind]): TreeNode[NodeKind] =
  TreeNode[NodeKind](kind: Immediate, val: i.uint32)
