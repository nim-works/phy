## Implements the translation of L3 code into LLVM IR (the textual form).

import
  std/[
    strutils,
    strformat,
    sets,
    tables
  ],
  passes/[
    trees,
    syntax
  ],
  vm/utils

type

  NumericType = object
    kind: range[Int..Float]
    size: uint32

  LLVMTypeKind = enum
    ## Corresponds roughly to the LLVM types.
    ltVoid
    ltInt
    ltFloat
    ltDouble
    ltPtr
    ltAggregate

  LLVMType = object
    case kind: LLVMTypeKind
    of ltInt:
      width: int
    of ltAggregate:
      str: string ## the raw inline type definition
    of ltFloat, ltDouble, ltPtr, ltVoid:
      discard

  ValKind = enum
    vkConst ## some integer/float constant
    vkGlobal## some global value
    vkTemp  ## LLVM local
    vkFromGlobal ## LLVM local that holds a value loaded from a global
    vkExpr  ## raw expression

  Value = object
    typ: LLVMType
    case kind: ValKind
    of vkConst, vkGlobal, vkExpr:
      val: string
    of vkTemp, vkFromGlobal:
      id: int

  PassCtx = object
    ## Context object for the pass. Available in most procedures.
    code: string
      ## full code for the module
    procs: seq[tuple[name: string, typ: NodeIndex]]
      ## for each procedure the name plus the cached type index

    # per procedure state:
    nextName: int
      ## ID to use for the next local LLVM name
    locals: seq[tuple[typ: NodeIndex, name: int]]
      ## all locals of the currently processed procedure
    deferred: Table[uint32, (uint32, Value)]
      ## maps block IDs to an assignment (represented by a local and value),
      ## which needs to be inserted at the start of the respective block

# give a name to some commonly LLVM types:
const
  PtrType   = LLVMType(kind: ltPtr)
  LBoolType = LLVMType(kind: ltInt, width: 1) # LLVM boolean
  BoolType  = LLVMType(kind: ltInt, width: 8)
  I32Type   = LLVMType(kind: ltInt, width: 32)

# shorten some common parameter definitions:
using
  c: var PassCtx
  tree: PackedTree[NodeKind]

func imm(n: TreeNode[NodeKind]): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

func id(n: TreeNode[NodeKind]): uint32 {.inline.} =
  assert n.kind in {Local, Global, Proc, ProcVal}
  n.val

func typ(n: TreeNode[NodeKind]): uint32 {.inline.} =
  assert n.kind == Type
  n.val

proc follow(tree; n: NodeIndex): NodeIndex =
  tree.child(tree.child(0), tree[n].typ)

proc sizeof(tree; n: NodeIndex): uint32 =
  ## Computes the size for the type at `n`.
  case tree[n].kind
  of Type:
    sizeof(tree, follow(tree, n))
  of Int, Float, UInt:
    tree[n].val
  of Ptr:
    8
  of Array, Record, Union:
    tree[n, 0].val
  else:
    unreachable()

proc alignof(tree; n: NodeIndex): uint32 =
  ## Computes the alignment for the type at `n`.
  case tree[n].kind
  of Type:
    alignof(tree, follow(tree, n))
  of Int, Float, UInt:
    tree[n].val
  of Ptr:
    8
  of Array, Record, Union:
    tree[n, 1].val
  else:
    unreachable()

proc formatValue(result: var string, t: LLVMType, spec: string) =
  ## Renders `t` and appends it to `result` (picked up by ``fmt``).
  case t.kind
  of ltVoid:   result.add "void"
  of ltFloat:  result.add "float"
  of ltDouble: result.add "double"
  of ltPtr:    result.add "ptr"
  of ltInt:
    result.add "i"
    result.addInt t.width
  of ltAggregate:
    result.add t.str

proc formatValue(result: var string, r: Value, spec: string) =
  ## Renders `r` and appends it to `result` (picked up by ``fmt``).
  if spec.len == 0:
    formatValue(result, r.typ, "")
    result.add " "

  case r.kind
  of vkConst, vkGlobal, vkExpr:
    result.add r.val
  of vkTemp, vkFromGlobal:
    result.add "%"
    result.addInt r.id

proc intConst(i: SomeInteger, typ: LLVMType): Value =
  if typ.kind == ltPtr and i == 0:
    Value(kind: vkConst, val: "null", typ: typ)
  else:
    Value(kind: vkConst, val: $i, typ: typ)

proc floatConst(f: float, typ: LLVMType): Value =
  Value(kind: vkConst, val: "0x" & toHex(cast[uint64](f)), typ: typ)

proc global(name: sink string, typ: LLVMType): Value =
  Value(kind: vkGlobal, val: name, typ: typ)

proc fullTy(tree; n: NodeIndex): LLVMType =
  ## Parses the type at `n` into an ``LLVMType``.
  case tree[n].kind
  of Type:
    fullTy(tree, follow(tree, n))
  of Record:
    var r = "{"
    var first = true
    for it in tree.items(n, 2):
      # TODO: padding is missing
      if not first:
        r.add ", "
      first = false
      r.formatValue(fullTy(tree, tree.child(it, 1)), "")
    r.add "}"
    LLVMType(kind: ltAggregate, str: r)
  of Array:
    LLVMType(kind: ltAggregate, str: fmt"[{tree[n, 2].imm} x {fullTy(tree, tree.child(n, 3))}]")
  of Union:
    # there are no unions in LLVM. A struct with the same size and alignment
    # as the union is emitted
    # find the most aligned member:
    var a = 0'u32
    var item: NodeIndex
    for it in tree.items(n, 2):
      if alignof(tree, it) >= a:
        a = alignof(tree, it)
        item = it

    if sizeof(tree, item) < sizeof(tree, n):
      # emit a struct containing the most aligned member + padding
      LLVMType(kind: ltAggregate, str:
        &"{{{fullTy(tree, item)}, [{sizeof(tree, n) - sizeof(tree, item)} x i8]}}")
    else:
      # no padding is needed
      fullTy(tree, item)
  of Int, UInt:
    LLVMType(kind: ltInt, width: int(tree[n].val * 8))
  of Ptr:
    LLVMType(kind: ltPtr)
  of Float:
    if tree[n].val == 4:
      LLVMType(kind: ltFloat)
    else:
      LLVMType(kind: ltDouble)
  of Void:
    LLVMType(kind: ltVoid)
  else:
    unreachable()

proc shortTy(tree; n: NodeIndex): LLVMType =
  ## Similar to `fullTy`, but uses identified types for aggregates.
  case tree[n].kind
  of Type:
    let nn = follow(tree, n)
    if tree[nn].kind in {Array, Record, Union}:
      LLVMType(kind: ltAggregate, str: "%Type_" & $tree[n].typ)
    else:
      shortTy(tree, nn)
  of Void, Int, UInt, Float, Ptr:
    fullTy(tree, n)
  else:
    unreachable()

proc toNumeric(tree; n: NodeIndex): NumericType =
  case tree[n].kind
  of Type:
    toNumeric(tree, follow(tree, n))
  of Int, Float, UInt:
    NumericType(kind: tree[n].kind, size: tree[n].val)
  else:
    unreachable()

proc isAggregateTy(tree; n: NodeIndex): bool =
  tree[n].kind in {Union, Array, Record} or
    (tree[n].kind == Type and isAggregateTy(tree, follow(tree, n)))

proc isFloatTy(tree; n: NodeIndex): bool =
  tree[n].kind == Float or
    (tree[n].kind == Type and isFloatTy(tree, follow(tree, n)))

proc isUnsignedTy(tree; n: NodeIndex): bool =
  tree[n].kind == UInt or
    (tree[n].kind == Type and isUnsignedTy(tree, follow(tree, n)))


proc emitOp(c; op: string) =
  c.code.add "  "
  c.code.add op
  c.code.add "\n"

proc emitOp(c; typ: LLVMType, op: string): Value =
  result = Value(kind: vkTemp, id: c.nextName, typ: typ)
  c.code.add "  %"
  c.code.addInt c.nextName
  c.code.add " = "
  c.code.add op
  c.code.add "\n"
  inc c.nextName

proc emitOp(c; tree; typ: NodeIndex, op: string): Value =
  result = Value(kind: vkTemp, id: c.nextName, typ: shortTy(tree, typ))
  c.code.add "  %"
  c.code.addInt c.nextName
  c.code.add " = "
  c.code.add op
  c.code.add "\n"
  inc c.nextName

proc emitLabel(c; label: string) =
  c.code.add label
  c.code.add ":\n"

proc use(c; id: uint32): Value =
  # locals are always allocated on the stack, meaning that the values have
  # type 'ptr'
   Value(kind: vkTemp, id: c.locals[id].name, typ: PtrType)

proc emitMemcpy(c; a, b, size: Value) =
  c.emitOp(fmt"call void @llvm.memcpy.i32({a}, {b}, {size}, i1 0)")

proc emitMemcpy(c; a, b: Value, size: uint32) =
  emitMemcpy(c, a, b, intConst(BiggestInt(size), I32Type))

proc emitMemclear(c; a, size: Value) =
  c.emitOp(fmt"call void @llvm.memset.i32({a}, i8 0, {size}, i1 0)")

proc emitLoad(c; tree; typ: NodeIndex, a: Value): Value =
  let t = shortTy(tree, typ)
  c.emitOp(t, fmt"load {t}, ptr {a:raw}")

proc emitStore(c; tree; typ: NodeIndex, dst, val: Value) =
  c.emitOp(fmt"store {val}, ptr {dst:raw}")

proc genExpr(c; tree; val: NodeIndex, typ = LLVMType(kind: ltVoid)): Value

proc receive(c; tree; n: NodeIndex, typ: LLVMType): Value {.inline.} =
  ## Same as ``genExpr``, but with an additional type check.
  result = genExpr(c, tree, n, typ)
  # sanity check
  assert result.typ.kind == typ.kind

proc genCall(c; tree; call: NodeIndex,
             start: int, fin: BackwardsIndex): (LLVMType, string) =
  ## Generates (but doesn't emit) the code for a call. `start` and `fin` are
  ## where the relevant parts of the list in `call` start and end,
  ## respectively.
  var args = ""
  var callee: Value
  var typ: NodeIndex
  if tree[call, start].kind == Proc:
    # it's a static call
    typ = c.procs[tree[call, start].id].typ
    var i = 1
    for it in tree.items(call, start + 1, fin):
      let v = c.receive(tree, it, shortTy(tree, tree.child(typ, i)))
      if args.len > 0:
        args.add ", "
      args.formatValue(v, "")
      inc i

    callee = global(c.procs[tree[call, start].id].name, PtrType)
  else:
    # it's an indirect call
    typ = follow(tree, tree.child(call, start))
    var i = 1
    for it in tree.items(call, start + 2, fin):
      let v = c.receive(tree, it, shortTy(tree, tree.child(typ, i)))
      if args.len > 0:
        args.add ", "
      args.formatValue(v, "")
      inc i

    callee = c.receive(tree, tree.child(call, start + 1), PtrType)

    # add a null guard
    # TODO: mark the null case as unlikely
    let cond = c.emitOp(LBoolType, fmt"icmp eq {callee}, null")
    c.emitOp(fmt"br i1 {cond:raw}, label %{c.nextName}, label %{c.nextName+1}")
    c.emitLabel($c.nextName)
    c.emitOp("call void @llvm.trap()")
    c.emitOp("unreachable")
    c.emitLabel($(c.nextName + 1))
    inc c.nextName, 2

  result[0] = shortTy(tree, tree.child(typ, 0))
  result[1] = fmt"{result[0]} {callee:raw}({args})"

proc operandTriple(tree; n: NodeIndex): (LLVMType, NodeIndex, NodeIndex, NodeIndex) =
  let (a, b, c) = triplet(tree, n)
  (shortTy(tree, a), a, b, c)

proc genBinaryOp(c; tree; n: NodeIndex, i, u, f: string): Value =
  ## Generates the code for a two-operand operation, with the opcode picked
  ## based on the type.
  let
    (typ, ot, a, b) = operandTriple(tree, n)
    av = c.receive(tree, a, typ)
    bv = c.receive(tree, b, typ)
  if isFloatTy(tree, ot):
    c.emitOp(typ, fmt"{f} {av}, {bv:raw}")
  elif isUnsignedTy(tree, ot):
    c.emitOp(typ, fmt"{u} {av}, {bv:raw}")
  else:
    c.emitOp(typ, fmt"{i} {av}, {bv:raw}")

proc genBinaryOp(c; tree; n: NodeIndex, op: string): Value =
  ## Generates the code for a two-operand operation.
  let
    (typ, _, a, b) = operandTriple(tree, n)
    av = c.receive(tree, a, typ)
    bv = c.receive(tree, b, typ)
  c.emitOp(typ, fmt"{op} {av}, {bv:raw}")

proc toBool(c; r: sink Value): Value =
  ## Converts an LLVM boolean (i1) value to an L4 boolean (i8).
  c.emitOp(BoolType, fmt"zext {r} to i8")

proc genCmpOp(c; tree; op: NodeIndex, i, u, f: string): Value =
  let (typ, ot, a, b) = operandTriple(tree, op)
  let av = c.receive(tree, a, typ)
  let bv = c.receive(tree, b, typ)
  if isFloatTy(tree, ot):
    c.emitOp(LBoolType, fmt"{f} {av}, {bv:raw}")
  elif isUnsignedTy(tree, ot):
    c.emitOp(LBoolType, fmt"{u} {av}, {bv:raw}")
  else:
    c.emitOp(LBoolType, fmt"{i} {av}, {bv:raw}")

proc genAsgn(c; tree; id: uint32, src: sink Value) =
  ## Emits an assignment of `src` to the local with the given id.
  let typ = c.locals[id].typ
  if isAggregateTy(tree, typ):
    c.emitMemcpy(c.use(id), src, sizeof(tree, typ))
  else:
    c.emitStore(tree, typ, c.use(id), src)

proc genPath(c; tree; n: NodeIndex): Value =
  ## Emits the 'getelementptr' operation(s) for the ``Path`` at `n`.
  var (val, typ) =
    if tree[n, 1].kind == Local:
      (c.use(tree[n, 1].id), c.locals[tree[n, 1].id].typ)
    else:
      (c.receive(tree, tree.child(n, 1), PtrType),
       tree.child(tree.child(n, 1), 0))

  var ltype = shortTy(tree, typ)
  var r = ", i32 0"

  if tree[typ].kind == Type:
    typ = follow(tree, typ)

  for it in tree.items(n, 2):
    case tree[typ].kind
    of Record:
      typ = tree.child(tree.child(typ, 2 + tree[it].val), 1)
      r.add ", i32 "
      r.addInt tree[it].val
    of Union:
      typ = tree.child(typ, 2 + tree[it].val)
      # LLVM doesn't have union types, so we cast the pointer-to-union
      # to the active type
      val = c.emitOp(PtrType, fmt"getelementptr {ltype}, {val}{r}")
      r = ", i32 0"
      ltype = shortTy(tree, typ)
    of Array:
      typ = tree.child(typ, 3)
      r.add ", "
      # literal values use i32 in this context
      r.formatValue(c.genExpr(tree, it, I32Type), "")
    else:
      unreachable()

    if tree[typ].kind == Type:
      typ = follow(tree, typ)

  c.emitOp(PtrType, fmt"getelementptr {ltype}, {val}{r}")

proc genCheckedOp(c; tree; n: NodeIndex, name: string): Value =
  ## Generates and emits the code for a checked arithmetic operation.
  let (typ, _, a, b) = operandTriple(tree, n)
  let av = c.receive(tree, a, typ)
  let bv = c.receive(tree, b, typ)
  let tv = LLVMType(kind: ltAggregate, str: fmt"{{{typ}, i1}}")
  let tmp = c.emitOp(tv, fmt"call {tv} @{name}.{typ}({av}, {bv})")
  c.genAsgn(tree, tree[n, 3].id, Value(kind: vkExpr, val: fmt"extractvalue {tmp}, 0"))
  c.toBool c.emitOp(LBoolType, fmt"extractvalue {tmp}, 1")

proc genShift(c; tree; n: NodeIndex, u, s: string): Value =
  ## Generates and emits the code for a left- or right-shift operation.
  let (typ, ot, a, b) = operandTriple(tree, n)
  let av = c.receive(tree, a, typ)
  # a different type is allowed for the RHS. It's converted to the correct
  # size first
  var bv = c.genExpr(tree, b, typ)
  if av.typ.width > bv.typ.width:
    bv = c.emitOp(av.typ, fmt"zext {bv} to {av.typ}")
  elif av.typ.width < bv.typ.width:
    bv = c.emitOp(av.typ, fmt"trunc {bv} to {av.typ}")

  # XXX: the L3 doesn't specify what the result of shl should be when the
  #      shift value is larger than the destination's width. We use the
  #      modulus of the distance to make the result well-defined
  let tmp = c.emitOp(bv.typ, fmt"and {bv}, {typ.width - 1}")
  if isUnsignedTy(tree, ot):
    c.emitOp(typ, fmt"{u} {av}, {tmp:raw}")
  else:
    c.emitOp(typ, fmt"{s} {av}, {tmp:raw}")

proc genExpr(c; tree; val: NodeIndex, typ: LLVMType): Value =
  ## Generates and emits the code for an expression (`val`).
  case tree[val].kind
  of IntVal:
    intConst(tree.getInt(val), typ)
  of Immediate:
    intConst(tree[val].imm, typ)
  of FloatVal:
    floatConst(tree.getFloat(val), typ)
  of ProcVal:
    global(c.procs[tree[val].id].name, PtrType)
  of Global:
    let typ = tree.child(tree.child(tree.child(1), tree[val].id), 0)
    # globals in LLVM are always pointers to a location, so a load is required
    # to get the actual value
    let tmp = c.emitLoad(tree, typ, global("@g" & $tree[val].id, PtrType))
    # remember that the value came from a global:
    Value(kind: vkFromGlobal, id: tmp.id, typ: tmp.typ)
  of Copy:
    case tree[val, 0].kind
    of Path:
      if isAggregateTy(tree, tree.child(tree.child(val, 0), 0)):
        # the actual copy (or not) is handled by the receiver
        c.genPath(tree, tree.child(val, 0))
      else:
        let v = c.genPath(tree, tree.child(val, 0))
        c.emitLoad(tree, tree.child(tree.child(val, 0), 0), v)
    of Local:
      let src = c.use(tree[val, 0].id)
      if isAggregateTy(tree, c.locals[tree[val, 0].id].typ):
        src
      else:
        c.emitLoad(tree, c.locals[tree[val, 0].id].typ, src)
    of Global:
      c.genExpr(tree, tree.child(val, 0))
    else:
      unreachable()
  of Addr:
    if tree[val, 0].kind == Path:
      c.genPath(tree, tree.child(val, 0))
    else:
      # all locals are represented as a pointer-to-stack-loc
      c.use(tree[tree.child(val, 0)].id)
  of Deref:
    # the receiver does the actual dereferencing (or not)
    c.receive(tree, tree.child(val, 1), PtrType)
  of Load:
    let (typ, a) = pair(tree, val)
    let x = c.receive(tree, a, PtrType)
    if isAggregateTy(tree, typ):
      x
    else:
      c.emitLoad(tree, typ, x)
  of Neg:
    let (typ, operand) = pair(tree, val)
    let inp = c.receive(tree, operand, shortTy(tree, typ))
    if isFloatTy(tree, typ):
      c.emitOp(tree, typ, fmt"fneg {inp}")
    else:
      # compute the two's complement
      let x = c.emitOp(tree, typ, fmt"xor {inp}, -1")
      c.emitOp(tree, typ, fmt"add {x}, 1")
  of Add:
    c.genBinaryOp(tree, val, "add", "add", "fadd")
  of Sub:
    c.genBinaryOp(tree, val, "sub", "sub", "fsub")
  of Mul:
    c.genBinaryOp(tree, val, "mul", "mul", "fmul")
  of Div:
    c.genBinaryOp(tree, val, "sdiv", "udiv", "fdiv")
  of Mod:
    c.genBinaryOp(tree, val, "srem", "urem", "frem")
  of AddChck:
    genCheckedOp(c, tree, val, "llvm.sadd.overflow")
  of SubChck:
    genCheckedOp(c, tree, val, "llvm.ssub.overflow")
  of MulChck:
    genCheckedOp(c, tree, val, "llvm.smul.overflow")
  of BitNot:
    let (typ, operand) = pair(tree, val)
    let x = c.receive(tree, operand, shortTy(tree, typ))
    c.emitOp(x.typ, fmt"xor {x}, -1")
  of BitAnd:
    c.genBinaryOp(tree, val, "and")
  of BitOr:
    c.genBinaryOp(tree, val, "or")
  of BitXor:
    c.genBinaryOp(tree, val, "xor")
  of Shl:
    c.genShift(tree, val, "shl", "shl")
  of Shr:
    c.genShift(tree, val, "lshr", "ashr")
  of Not:
    let v = c.genExpr(tree, tree.child(val, 0), BoolType)
    c.toBool c.emitOp(LBoolType, fmt"icmp eq {v}, 0")
  of Eq:
    c.toBool c.genCmpOp(tree, val, "icmp eq", "icmp eq", "fcmp ueq")
  of Lt:
    c.toBool c.genCmpOp(tree, val, "icmp slt", "icmp ult", "fcmp ult")
  of Le:
    c.toBool c.genCmpOp(tree, val, "icmp sle", "icmp ule", "fcmp ule")
  of Reinterp:
    # reinterpret the bit pattern as another type
    let (dtyp, styp, a) = triplet(tree, val)
    let v = c.receive(tree, a, shortTy(tree, styp))
    let ltyp = shortTy(tree, dtyp)
    # pointers require special conversions
    if ltyp.kind == ltPtr:
      if v.kind in {vkConst, vkFromGlobal}:
        # treat the constant as an offset into the static memory region
        # XXX: this is a temporary workaround to make the code generated by
        #      skully work
        c.emitOp(PtrType, fmt"getelementptr i8, ptr @phy_mem, {v}")
      else:
        c.emitOp(ltyp, fmt"inttoptr {v} to {ltyp}")
    elif v.typ.kind == ltPtr:
      c.emitOp(ltyp, fmt"ptrtoint {v} to {ltyp}")
    else:
      c.emitOp(ltyp, fmt"bitcast {v} to {ltyp}")
  of Conv:
    # numeric conversion
    let (dtyp, styp, a) = triplet(tree, val)
    let ltyp = shortTy(tree, dtyp)
    let x = c.genExpr(tree, a, shortTy(tree, styp))
    let dst = toNumeric(tree, dtyp)
    let src = toNumeric(tree, styp)
    # NOTE: the conversion from signed-to-unsigned (and vice versa), as well
    # as float-to-int are not well-defined at the moment, invoking undefined
    # behaviour at the LLVM side
    case dst.kind
    of Int:
      case src.kind
      of Int, UInt:
        if src.size < dst.size:
          c.emitOp(ltyp, fmt"sext {x} to {ltyp}")
        elif src.size > dst.size:
          c.emitOp(ltyp, fmt"trunc {x} to {ltyp}")
        else:
          x
      of Float:
        c.emitOp(ltyp, fmt"fptosi {x} to {ltyp}")
    of UInt:
      case src.kind
      of Int, UInt:
        if src.size < dst.size:
          c.emitOp(ltyp, fmt"zext {x} to {ltyp}")
        elif src.size > dst.size:
          c.emitOp(ltyp, fmt"trunc {x} to {ltyp}")
        else:
          x
      of Float:
        c.emitOp(ltyp, fmt"fptoui {x} to {ltyp}")
    of Float:
      case src.kind
      of Int:
        c.emitOp(ltyp, fmt"sitofp {x} to {ltyp}")
      of UInt:
        c.emitOp(ltyp, fmt"uitofp {x} to {ltyp}")
      of Float:
        if src.size == 8:
          c.emitOp(ltyp, fmt"fptrunc {x} to float")
        else:
          c.emitOp(ltyp, fmt"fpext {x} to double")
  of Call:
    let (typ, call) = c.genCall(tree, val, 0, ^1)
    c.emitOp(typ, "call " & call)
  else:
    unreachable()

proc genExit(c; tree; exit: NodeIndex) =
  ## Generates and emits the code for a basic-block exit.
  case tree[exit].kind
  of Goto, Loop:
    c.emitOp(fmt"br label %L{tree[exit, 0].imm}")
  of Return:
    if tree.len(exit) == 1:
      let v = c.genExpr(tree, tree.child(exit, 0))
      c.emitOp(fmt"ret {v}")
    else:
      c.emitOp("ret void")
  of Raise:
    let v = c.receive(tree, tree.child(exit, 0), PtrType)
    if tree[exit, 1].kind == Unwind:
      c.emitOp(fmt"call void @phy_raise({v})")
      c.emitOp("unreachable")
    else:
      c.emitOp(fmt"invoke void @phy_raise({v}) to label %{c.nextName} unwind label %L{tree[tree.child(exit, 1), 0].imm}")
      c.emitLabel($c.nextName)
      c.emitOp("unreachable")
      inc c.nextName
  of Branch:
    let (sel, a, b) = triplet(tree, exit)
    let cond = c.receive(tree, sel, BoolType)
    let tmp = c.emitOp(LBoolType, fmt"trunc {cond} to i1")
    c.emitOp(fmt"br i1 {tmp:raw}, label %L{tree[b, 0].imm}, label %L{$tree[a, 0].imm}")
  of Select:
    # TODO: implement
    unreachable("missing")
  of CheckedCall:
    let (_, call) = c.genCall(tree, exit, 0, ^3)
    if tree[tree.child(exit, ^1)].kind == Unwind:
      # no local exception handler
      c.emitOp("call " & call)
      c.emitOp("br label %L" & $tree[tree.child(exit, ^2), 0].imm)
    else:
      c.emitOp(fmt"invoke {call} to label %L{$tree[tree.child(exit, ^2), 0].imm} unwind label %L{$tree[tree.child(exit, ^1), 0].imm}")
  of CheckedCallAsgn:
    let (typ, call) = c.genCall(tree, exit, 1, ^3)
    if tree[tree.child(exit, ^1)].kind == Unwind:
      # no local exception handler
      let tmp = c.emitOp(typ, "call " & call)
      c.genAsgn(tree, tree[exit, 0].id, tmp)
      c.emitOp("br label %L" & $tree[tree.child(exit, ^2), 0].imm)
    else:
      let tmp = c.emitOp(typ, fmt"invoke {call} to label %L{$tree[tree.child(exit, ^2), 0].imm} unwind label %L{$tree[tree.child(exit, ^1), 0].imm}")
      # a direct assignment is not possible. Instead, the assignment must be
      # part of the target basic block
      c.deferred[tree[tree.child(exit, ^2), 0].imm] = (tree[exit, 0].id, tmp)
  of Unreachable:
    # important: the L3 unreachable does not directly map to the LLVM
    # unreachable
    c.emitOp("call void @llvm.trap()")
    c.emitOp("unreachable")
  else:
    unreachable()

proc genStmt(c; tree; n: NodeIndex) =
  ## Generates the bytecode for a statement (`n`).
  case tree[n].kind
  of Asgn:
    let (a, b) = pair(tree, n)
    let (typ, dst) =
      case tree[a].kind
      of Path:  (tree.child(a, 0),         c.genPath(tree, a))
      of Local: (c.locals[tree[a].id].typ, c.use(tree[a].id))
      else:     unreachable()

    if isAggregateTy(tree, typ):
      let src = c.receive(tree, b, PtrType)
      c.emitMemcpy(dst, src, sizeof(tree, typ))
    else:
      let src = c.receive(tree, b, shortTy(tree, typ))
      c.emitStore(tree, typ, dst, src)
  of Store:
    let (typ, ot, a, b) = operandTriple(tree, n)
    let dst = c.receive(tree, a, PtrType)
    if isAggregateTy(tree, ot):
      let src = c.receive(tree, b, PtrType)
      c.emitMemcpy(dst, src, sizeof(tree, ot))
    else:
      let src = c.receive(tree, b, typ)
      c.emitStore(tree, ot, dst, src)
  of Clear:
    let x = c.receive(tree, tree.child(n, 0), PtrType)
    let y = c.genExpr(tree, tree.child(n, 1), I32Type)
    c.emitMemclear(x, y)
  of Blit:
    let x = c.receive(tree, tree.child(n, 0), PtrType)
    let y = c.receive(tree, tree.child(n, 1), PtrType)
    let z = c.genExpr(tree, tree.child(n, 2), I32Type)
    # XXX: are the blit arguments guaranteed to not overlap?
    c.emitMemcpy(x, y, z)
  of Call:
    let (_, call) = c.genCall(tree, n, 0, ^1)
    c.emitOp("call " & call)
  of Drop:
    # genExpr always emits either a constant or a temp, so dropping the
    # value just means doing nothing with it
    discard c.genExpr(tree, tree.child(n, 0))
  else:
    unreachable()

proc gen(c; tree; n: NodeIndex) =
  ## Generates the code for a basic block.
  case tree[n].kind
  of Except:
    # XXX: exception handling is unfinished
    let tmp = c.emitOp(PtrType, "landingpad ptr catch ptr null")
    # assign the exception pointer to the local specified as the
    # block parameter:
    c.genAsgn(tree, tree[tree.child(tree.child(n, 0), 0)].id, tmp)
    c.emitOp("call void @phy_catch()")
  of Block:
    discard "nothing to do"
  else:
    unreachable()

  for it in tree.items(n, 1, ^2):
    genStmt(c, tree, it)

  c.genExit(tree, tree.last(n))

proc translate(c; tree; def: NodeIndex) =
  ## Generates the code for the single procedure `def`.
  let (_, locals, blocks) = tree.triplet(def)

  # reserve the slots for the locals:
  c.locals.setLen(tree.len(locals))
  # reserve the parameter names:
  c.nextName = tree.len(tree.child(tree.child(blocks, 0), 0))

  c.emitOp("entry:")

  # set up all locals. We don't bother with SSA or allocating vars in the
  # first-used basic-block. Instead, all locals are stack-allocated in the
  # entry block
  for i, it in tree.pairs(locals):
    let tmp = c.emitOp(PtrType, fmt"alloca {shortTy(tree, it)}")
    c.locals[i] = (it, tmp.id)

  # set up the parameters. In the L3, parameters are mutable callee-side
  # variables, but in LLVM functions they're not. The actual parameter
  # values need to be copied into the locations first
  for i, it in tree.pairs(tree.child(tree.child(blocks, 0), 0)):
    let
      id = tree[it].id
      typ = Value(kind: vkTemp, id: i, typ: shortTy(tree, c.locals[id].typ))
    c.genAsgn(tree, id, typ)

  c.emitOp("br label %L0")

  for i, it in tree.pairs(blocks):
    c.emitLabel("L" & $i)
    # emit the deferred assignment, if one exists:
    var p: (uint32, Value)
    if c.deferred.pop(i.uint32, p):
      c.genAsgn(tree, p[0], p[1])

    c.gen(tree, it)

proc sig(tree; n: NodeIndex): (LLVMType, seq[LLVMType]) =
  ## Returns the LLVM types for the ``ProcTy`` at `n`.
  result[0] = shortTy(tree, tree.child(n, 0))
  for it in tree.items(n, 1):
    result[1].add shortTy(tree, it)

proc mangle(name: string): string =
  name.replace('.', '_')

proc translate*(module: PackedTree[NodeKind]): string =
  ## Translates a complete module to the VM bytecode and the associated
  ## environmental data.
  let (types, globals, procs) = module.triplet(NodeIndex(0))

  var c = PassCtx()
  c.procs.newSeq(module.len(procs))

  # emit the EH helper routines declarations. Their actual definition needs to
  # be provided separately:
  c.code.add "declare void @phy_raise(ptr)\n"
  c.code.add "declare void @phy_catch()\n"
  c.code.add "declare i32 @phy_eh_personality(...)\n"

  # create identified types for all aggregates:
  for i, it in module.pairs(types):
    if module.isAggregateTy(it):
      c.code.add &"%Type_{i} = type {fullTy(module, it)}\n"

  # handle the exports, if any:
  if module.len(NodeIndex 0) == 4:
    let exports = module.next(procs)
    var memSize = 1024'i64
    for it in module.items(exports):
      case module.getString(module.child(it, 0))
      of "total_memory":
        memSize = module.getInt(module.child(module.child(globals, module[it, 1].id), 1))
      else:
        # use the export name as the procedure name
        if module[it, 1].kind == Proc:
          c.procs[module[it, 1].id].name = "@" & mangle(module.getString(module.child(it, 0)))

    # heap memory is emulated via a fixed-size static memory region, with the
    # size given by a global
    c.code.add &"@phy_mem = private global [{memSize} x i8] zeroinitializer, align 8\n"

  # add the defined globals to the environment:
  for i, def in module.pairs(globals):
    let (typ, val) = module.pair(def)
    # globals are currently immutable
    c.code.add &"@g{i} = private constant {c.genExpr(module, val, shortTy(module, typ))}\n"

  var imports: HashSet[string]

  # generate the procedure names and emit the imports:
  for i, def in module.pairs(procs):
    let typ = follow(module, module.child(def, 0))
    if module[def].kind == ProcDef:
      if c.procs[i].name.len == 0:
        # only generate a name if the procedure doesn't have one yet
        c.procs[i].name = "@p" & $i
      c.procs[i].typ = typ
    else:
      let name = mangle(module.getString(module.child(def, 1)))
      # the same function may be imported multiple times; only emit a
      # declaration once
      if not imports.containsOrIncl(name):
        let (ret, params) = sig(module, typ)
        c.code.add fmt"declare {ret} @{name}("
        for j, it in params.pairs:
          if j > 0:
            c.code.add ", "
          c.code.formatValue(it, "")
        c.code.add ")\n"

      c.procs[i] = ("@" & name, typ)

  # generate the code for the procedures and add them to the environment:
  for i, def in module.pairs(procs):
    if module[def].kind == ProcDef:
      let (ret, params) = sig(module, c.procs[i].typ)
      c.code.add fmt"define hidden {ret} {c.procs[i].name}("

      for j, it in params.pairs:
        if j > 0:
          c.code.add ", "
        c.code.formatValue(it, "")

      # to aid with debugging, request stack-smashing protection (=ssp) for all
      # procedures
      c.code.add ") ssp personality ptr @phy_eh_personality {\n"
      c.translate(module, def)
      c.code.add "}\n"

  # export the last L3 function as the Main procedure
  c.code.add &"@Main = external alias ptr, ptr {c.procs[module.len(procs)-1].name}\n"
  result = c.code
