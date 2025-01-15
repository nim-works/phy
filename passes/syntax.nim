## Provides the type definitions for the various intermediate languages.

# XXX: this module is going be auto-generated by the (not yet implemented)
#      language grammar management tool

import
  experimental/sexp,
  passes/trees,
  vm/utils

type
  NodeKind* = enum
    Immediate, IntVal, FloatVal, StringVal, ProcVal, Proc, Type, Local, Global
    Int, UInt, Float

    List

    Void, ProcTy, Blob, Record, Union, Array

    Join

    Asgn, Drop, Clear, Blit

    Load, Store, Addr, Call
    Deref, Field, At, Path
    Copy

    Neg, Add, Sub, Mul, Div, Mod
    AddChck, SubChck, MulChck

    Not, Eq, Le, Lt
    BitAnd, BitNot, BitXor, BitOr
    Shl, Shr

    Conv, Reinterp

    Goto, Loop, Raise, Unreachable, Select, Branch
    CheckedCall, CheckedCallAsgn, Unwind, Choice

    Module, TypeDefs, ProcDefs, ProcDef, Locals,
    Except, Params, GlobalDefs, GlobalDef, Import, Export

    Break, Return, Case, If, Block, Stmts

  Node = TreeNode[NodeKind]

using
  lit: var Literals

template isAtom*(x: NodeKind): bool =
  ord(x) <= ord(Float)

proc toSexp*(tree: PackedTree[NodeKind], idx: NodeIndex,
             n: TreeNode[NodeKind]): SexpNode =
  case n.kind
  of Immediate: sexp(n.val.int)
  of IntVal:    sexp([newSSymbol("IntVal"), sexp tree.getInt(idx)])
  of FloatVal:  sexp([newSSymbol("FloatVal"), sexp tree.getFloat(idx)])
  of StringVal: sexp([newSSymbol("StringVal"), sexp tree.getString(idx)])
  of ProcVal:   sexp([newSSymbol("ProcVal"), sexp n.val.int])
  of Proc:      sexp([newSSymbol("Proc"), sexp n.val.int])
  of Type:      sexp([newSSymbol("Type"), sexp n.val.int])
  of Local:     sexp([newSSymbol("Local"), sexp n.val.int])
  of Global:    sexp([newSSymbol("Global"), sexp n.val.int])
  of Int:       sexp([newSSymbol("Int"), sexp n.val.int])
  of UInt:      sexp([newSSymbol("UInt"), sexp n.val.int])
  of Float:     sexp([newSSymbol("Float"), sexp n.val.int])
  else:         unreachable()

proc fromSexp*(kind: NodeKind): Node =
  raise ValueError.newException($kind & " node is missing operand")

proc fromSexp*(kind: NodeKind, val: BiggestInt, lit): Node =
  case kind
  of IntVal:
    Node(kind: kind, val: lit.pack(val))
  of ProcVal, Proc, Type, Local, Global, Int, UInt, Float:
    Node(kind: kind, val: val.uint32)
  else:
    unreachable()

proc fromSexp*(kind: NodeKind, val: BiggestFloat, lit): Node =
  assert kind == FloatVal
  Node(kind: kind, val: lit.pack(val))

proc fromSexp*(kind: NodeKind, val: string, lit): Node =
  assert kind == StringVal
  Node(kind: kind, val: lit.pack(val))

proc fromSexp*(_: typedesc[NodeKind], val: BiggestInt, lit): Node =
  Node(kind: Immediate, val: val.uint32)

proc fromSexp*(_: typedesc[NodeKind], val: BiggestFloat, lit): Node =
  Node(kind: FloatVal, val: lit.pack(val))

proc fromSexp*(_: typedesc[NodeKind], val: string, lit): Node =
  Node(kind: StringVal, val: lit.pack(val))

proc fromSexpSym*(_: typedesc[NodeKind], val: string, lit): Node =
  raise ValueError.newException("standalone S-expr symbols are not supported")