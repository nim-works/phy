## Implements an IR for the highest-level IL that's not flat. It's meant as a
## helper for ``source2il``, to make tree construction easier and less prone
## to mistakes. The IR is meant to be a temporary measure until more lowering
## is delegated to separate passes.
##
## Some common things, like wrapping lvalue expression in a `Copy` operation
## when appearing in a usage context, are handled during to-packed-tree
## translation.

import
  passes/[builders, spec, trees],
  vm/utils

type
  IrNode* = object
    case kind*: NodeKind
    of IntVal:
      intVal*: int
    of FloatVal:
      floatVal*: float
    of Local, Proc, Type:
      id*: uint32
    of Field, At, Deref, Addr, Call, Stmts, Drop, Asgn, Break, Return, Loop,
       If, Case, Choice, Add, Sub, Mul, Div, Mod, Not, Eq, Lt, Le,
       AddChck, SubChck, MulChck:
      children*: seq[IrNode]
    else:
      discard

  Node = TreeNode[NodeKind]

const None* = Immediate
  ## Represents an uninitialized node

template `[]`*(n: IrNode, i: int): IrNode =
  n.children[i]

template add*(n: var IrNode, elem: IrNode) =
  ## Adds `elem` to `n`. The expression passed to `elem` is allowed to
  ## modify `n`.
  let tmp = elem
  n.children.add tmp

template add*(n: var IrNode, elems: seq[IrNode]) =
  ## Adds `elems` to `n`. The expression passed to `elem` is allowed to
  ## modify `n`.
  let tmp = elems
  n.children.add tmp

proc newIntVal*(v: BiggestInt): IrNode =
  IrNode(kind: IntVal, intVal: v.int)

proc newFloatVal*(val: float): IrNode =
  IrNode(kind: FloatVal, floatVal: val)

proc newLocal*(id: uint32): IrNode =
  IrNode(kind: Local, id: id)

proc newTypeUse*(id: uint32): IrNode =
  IrNode(kind: Type, id: id)

proc newIf*(cond, then, els: sink IrNode): IrNode =
  IrNode(kind: If, children: @[cond, then, els])

proc newIf*(cond, then: sink IrNode): IrNode =
  IrNode(kind: If, children: @[cond, then])

proc newChoice*(val, then: sink IrNode): IrNode =
  IrNode(kind: Choice, children: @[val, then])

proc newCase*(typ: uint32, sel: sink IrNode): IrNode =
  IrNode(kind: Case, children: @[newTypeUse(typ), sel])

proc newAsgn*(dest, src: sink IrNode): IrNode =
  # allow none for the sake of error correction
  assert dest.kind in {Field, At, Local, Deref, None}
  IrNode(kind: Asgn, children: @[dest, src])

proc newFieldExpr*(n: sink IrNode, index: int): IrNode =
  assert n.kind in {Field, At, Local, Deref, None}
  IrNode(kind: Field, children: @[n, newIntVal(index)])

proc newAt*(lval, index: sink IrNode): IrNode =
  assert lval.kind in {Field, At, Local, Deref, None}
  IrNode(kind: At, children: @[lval, index])

proc newDeref*(typ: uint32, n: sink IrNode): IrNode =
  IrNode(kind: Deref, children: @[IrNode(kind: Type, id: typ), n])

proc newReturn*(n: sink IrNode): IrNode =
  IrNode(kind: Return, children: @[n])

proc newBreak*(depth: Natural): IrNode =
  IrNode(kind: Break, children: @[newIntVal(depth)])

proc newCall*(prc: uint32, arg: sink IrNode): IrNode =
  IrNode(kind: Call, children: @[IrNode(kind: Proc, id: prc), arg])

proc newCall*(prc: uint32, args: sink seq[IrNode]): IrNode =
  args.insert IrNode(kind: Proc, id: prc)
  IrNode(kind: Call, children: args)

proc newNot*(n: sink IrNode): IrNode =
  IrNode(kind: Not, children: @[n])

proc newDrop*(e: sink IrNode): IrNode =
  IrNode(kind: Drop, children: @[e])

proc newAddr*(e: sink IrNode): IrNode =
  IrNode(kind: Addr, children: @[e])

proc newUnreachable*(): IrNode =
  IrNode(kind: Unreachable)

proc newBinaryOp*(op: NodeKind, typ: uint32, a, b: sink IrNode): IrNode =
  case op
  of Add, Sub, Mul, Div, Mod, Eq, Lt, Le:
    IrNode(kind: op, children: @[IrNode(kind: Type, id: typ), a, b])
  else:
    unreachable()

proc newCheckedOp*(op: NodeKind, typ: uint32, a, b, dst: sink IrNode): IrNode =
  case op
  of AddChck, SubChck, MulChck:
    assert dst.kind == Local
    IrNode(kind: op, children: @[IrNode(kind: Type, id: typ), a, b, dst])
  else:
    unreachable()

proc convert*(n: IrNode, lit: var Literals, bu: var Builder[NodeKind])

proc use*(n: IrNode, lit: var Literals, bu: var Builder[NodeKind]) =
  ## Emits `n` to `bu`. If `n` is an lvalue expression, it's first turned
  ## into a proper rvalue expression.
  case n.kind
  of Field, At, Local:
    bu.subTree Copy:
      convert(n, lit, bu)
  of Deref:
    bu.subTree Load:
      convert(n[0], lit, bu)
      use(n[1], lit, bu)
  of Proc:
    bu.add Node(kind: ProcVal, val: n.id)
  else:
    convert(n, lit, bu)

proc convert*(n: IrNode, lit: var Literals, bu: var Builder[NodeKind]) =
  ## Emits `n` to `bu` as is.
  case n.kind
  of None:
    # okay, ignore. None should only be possible after error-correcting, in
    # which case the resulting code is not used anyway
    discard
  of IntVal:
    bu.add Node(kind: IntVal, val: lit.pack(n.intVal))
  of FloatVal:
    bu.add Node(kind: FloatVal, val: lit.pack(n.floatVal))
  of Field:
    bu.subTree Field:
      convert(n[0], lit, bu)
      bu.add Node(kind: Immediate, val: n[1].intVal.uint32)
  of At, Deref:
    bu.subTree n.kind:
      convert(n[0], lit, bu)
      use(n[1], lit, bu)
  of Drop, Not:
    bu.subTree n.kind:
      use(n[0], lit, bu)
  of Local, Proc, Type:
    bu.add Node(kind: n.kind, val: n.id)
  of Addr:
    if n[0].kind == Deref:
      # collapse `(Addr (Deref typ x))` to just `x`
      use(n[0][1], lit, bu)
    else:
      bu.subTree Addr:
        convert(n[0], lit, bu)
  of AddChck, SubChck, MulChck:
    bu.subTree n.kind:
      convert(n[0], lit, bu)
      use(n[1], lit, bu)
      use(n[2], lit, bu)
      convert(n[3], lit, bu)
  of Call:
    bu.subTree Call:
      for i, it in n.children.pairs:
        if i == 0:
          convert(it, lit, bu)
        else:
          use(it, lit, bu)
  of Asgn:
    if n[0].kind == Deref:
      # (Asgn (Deref typ x) y) -> (Store typ x y)
      bu.subTree Store:
        convert(n[0][0], lit, bu)
        use(n[0][1], lit, bu)
        use(n[1], lit, bu)
    else:
      bu.subTree Asgn:
        convert(n[0], lit, bu)
        use(n[1], lit, bu)
  of Break:
    bu.subTree Break:
      bu.add Node(kind: Immediate, val: n[0].intVal.uint32)
  of Return:
    bu.subTree Return:
      if n.children.len == 1:
        use(n[0], lit, bu)
  of Unreachable:
    bu.subTree Unreachable:
      discard
  of If:
    bu.subTree If:
      use(n[0], lit, bu)
      convert(n[1], lit, bu)
      if n.children.len == 3:
        convert(n[2], lit, bu)
  of Loop:
    bu.subTree Loop:
      convert(n[0], lit, bu)
  of Stmts:
    bu.subTree Stmts:
      for it in n.children.items:
        convert(it, lit, bu)
  else:
    bu.subTree n.kind:
      for it in n.children.items:
        use(it, lit, bu)
