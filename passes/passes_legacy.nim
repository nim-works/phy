
import nanopass/nanopass
import passes/literals
import std/[tables, intsets, options, algorithm]

type
  Local = distinct uint32
  Global = distinct uint32
  Proc = distinct uint32
  Type = distinct uint32

defineLanguage Lskully:
  ## Language for the code output by skully.
  int64(i)
  float64(fl)
  string(str)
  Local(lo)
  Global(g)
  Proc(pr) # proc is a reserved word
  Type(tid)

  field(f) ::= Field(i, t)
  typ(t) ::= tid | Int(i) | UInt(i) | Float(i) | Ptr() | Void() |
            Record(i, i, f, ...f) | Union(i, i, t, ...t) | Array(i, i, i, t) |
            ProcTy(t, ...t)

  lvalue(lv) ::= lo | g | Deref(t, e) | Field(lv, i) | At(lv, e)
  expr(e) ::= i | fl | ProcVal(i) |
              Call(t, e, ...e) | Call(pr, ...e) |
              Conv(t, t, e) | Reinterp(t, t, e) | Trunc(t, t, e) |
              Zext(t, t, e) | Sext(t, t, e) |
              Demote(t, t, e) | Promote(t, t, e) |
              Nil() |
              Load(t, e) | Copy(lv) | Addr(lv) |
              Add(t, e, e) | Sub(t, e, e) | Mul(t, e, e) | Div(t, e, e) | Mod(t, e, e) |
              BitNot(t, e) | BitAnd(t, e, e) | BitOr(t, e, e) | BitXor(t, e, e) |
              AddChck(t, e, e, lo) | SubChck(t, e, e, lo) | MulChck(t, e, e, lo) |
              Shl(t, e, e) | Shr(t, e, e) |
              Neg(t, e) |
              Not(e) |
              Eq(t, e, e) | Le(t, e, e) | Lt(t, e, e)

  goto(go) ::= Goto(i)

  target(tgt) ::= Goto(i) | Unwind()
  stmt(st) ::= Stmts(st, ...st) | Goto(i) | Join(i) |
               CheckedCall(t, e, ...e, tgt) |
               CheckedCall(pr, ...e, tgt) |
               CheckedCallAsgn(lo, t, e, ...e, tgt) |
               CheckedCallAsgn(lo, pr, ...e, tgt) |
               Call(pr, ...e) | Call(t, e, ...e) |
               Return() | Return(e) |
               Raise(e, tgt) |
               Branch(e, go, go) |
               Blit(e, e, e) | Clear(e, e) |
               Store(t, e, e) | Asgn(lv, e) | Except(i, lo) |
               Unreachable() |
               Loop(i) |
               Drop(e)

  params(p) ::= Params(...lo)
  locals(locs) ::= Locals(...t)

  init(ini) ::= Data(t, str) | Data(t)

  # the v
  decl(d) ::= Import(t, str) |
              ProcDef(t, p, locs, st) |
              GlobalDef(t, i) | GlobalDef(t, fl) |
              GlobalLoc(t, ini)
  exprt(exp) ::= Export(str, g) | Export(str, pr) # export is a reserved word

  #
  tdecls(td) ::= TypeDefs(...t)
  gdecls(gd) ::= GlobalDefs(...d)
  pdecls(pd) ::= ProcDefs(...d)
  exports(es) ::= List(...exp)

  module(m) ::= Module(td, gd, pd, es)

defineLanguage L6, Lskully:
  ## Language with basic blocks.
  bblock(bb) ::= +Block(p, ...st, ex) | +Except(p, ...st, ex)
  stmt(st) ::= -Return() |
               -Return(e) |
               -Goto(i) |
               -Raise(e, tgt) |
               -Loop(i) |
               -Unreachable() |
               -Join(i) |
               -Except(i, lo) |
               -CheckedCall(t, e, ...e, tgt) |
               -CheckedCall(pr, ...e, tgt) |
               -CheckedCallAsgn(lo, t, e, ...e, tgt) |
               -CheckedCallAsgn(lo, pr, ...e, tgt) |
               -Branch(e, go, go) |
               -Stmts(st, ...st)
  exit(ex) ::= +Return() | +Return(e) | +Goto(i) | +Raise(e, tgt) | +Branch(e, go, go) |
               +CheckedCall(t, e, ...e, go, tgt) |
               +CheckedCall(pr, ...e, go, tgt) |
               +CheckedCallAsgn(lo, t, e, ...e, go, tgt) |
               +CheckedCallAsgn(lo, pr, ...e, go, tgt) |
               +Unreachable() |
               +Loop(i)
  blocks(bl) ::= +List(bb, ...bb)
  decl(d) ::= -ProcDef(t, p, locs, st) | +ProcDef(t, locs, bl)

defineLanguage L5, L6:
  ## Language without mutable global locations.
  init(ini) ::= -Data(t) | -Data(t, str) | +Data(i, i) | +Data(i, str)
  decl(d) ::= -GlobalLoc(t, ini) | +GlobalDef(t, ini)
  lvalue(lv) ::= -g
  expr(e) ::= +Copy(g)

defineLanguage L4, L5:
  ## Language with combined, flat paths.
  root(ro) ::= +lo | +Deref(t, e)
  lvalue(lv) ::= -Field(lv, i) | -At(lv, e) | -Deref(t, e) |
                 +Path(t, ro, e, ...e)

defineLanguage L3s2, L4:
  ## Language without aggregate parameters.

defineLanguage L3s1, L3s2:
  ## Language without aggregate types.
  expr(e) ::= +Offset(e, e, e)
  typ(t) ::= +Blob(i, i) |
             -Record(i, i, f, ...f) |
             -Array(i, i, i, t) |
             -Union(i, i, t, ...t)
  lvalue(lv) ::= -Path(t, ro, e, ...e)

defineLanguage L3, L3s1:
  ## Language without primitive locals that can have their address taken.

defineLanguage L2, L3:
  ## Language without blob assignments.

defineLanguage L1, L2:
  ## Language with explicit stack management and only primitive types.
  typ(t) ::= -Blob(i, i)
  expr(e) ::= -Addr(lv)
  decl(d) ::= -ProcDef(t, locs, bl) |
              +ProcDef(t, i, locs, bl)

defineLanguage LPtr, L1:
  ## Language where only proc types are identified.

defineLanguage L0, LPtr:
  ## Language without pointer types and related operations.
  typ(t) ::= -Ptr()
  expr(e) ::= -Nil() | -Offset(e, e, e)

# terminal adapter routines:
template defineTerminal(typ: typedesc) {.dirty.} =
  template unpack(lit: Literals, id: uint32, _: typedesc[typ]): typ =
    typ(id)
  template pack(lit: var Literals, val: typ): uint32 =
    uint32(val)

defineTerminal(Local)
defineTerminal(Global)
defineTerminal(Proc)
defineTerminal(Type)

template map[T, U](x: ChildSlice[T, auto], p: proc(x: T): U): seq[U] =
  let cs = x
  var s = newSeq[U](cs.len)
  for i, it in x.pairs:
    s[i] = p(it)
  s

template mapIt[T](x: ChildSlice[T, auto], body: untyped): untyped =
  let cs = x
  var s = newSeq[
    typeof(
      block:
        var it {.inject.}: T
        body
        it)
    ](cs.len)
  for i, it {.inject.} in x.pairs:
    s[i] = body
  s

proc basicBlocks(ir: Lskully): L6 {.pass.} =
  ## Transforms the bodies of procedures into a basic-block-oriented structure.

  proc target(x: src.tgt, map: Table[int64, int]): dst.tgt =
    match x:
    of Goto(i): build dst.tgt, Goto(i(^map[i.val]))
    of Unwind(): build dst.tgt, Unwind()

  proc goto(x: src.go, map: Table[int64, int]): dst.go =
    match x:
    of Goto(i): build dst.go, Goto(i(^map[i.val]))

  type BBlock = object
    isExcept: bool
    params: dst.p
    stmts: seq[dst.st]

  proc blocks(x: src.st, bbs: var seq[dst.bb], bb: var BBlock, map: Table[int64, int]) =
    proc commitBlock(bbs: var seq[dst.bb], bb: var BBlock, ex: dst.ex) =
      if bb.isExcept:
        bbs.add build(dst.bb, Except(^bb.params, ...bb.stmts, ex))
      else:
        bbs.add build(dst.bb, Block(^bb.params, ...bb.stmts, ex))
      bb.stmts.shrink(0)

    proc startBlock(bb: var BBlock) =
      bb.isExcept = false
      bb.params = build(dst.p, Params([]))

    match x:
    of Stmts(...st):
      for it in st.items:
        blocks(it, bbs, bb, map)
    of Goto(i):
      commitBlock bbs, bb, build(dst.ex, Goto(i(^map[i.val])))
    of Join(i):
      # don't merge an empty entry block with the following block; the latter
      # might be a loop start
      if map[i.val] > bbs.len:
        commitBlock bbs, bb, build(dst.ex, Goto(i(^map[i.val])))
      startBlock(bb)
    of Except(_, lo):
      assert bb.stmts.len == 0, "control flow falls through into exception handler"
      bb.isExcept = true
      bb.params = build(dst.p, Params([lo]))
    of Asgn([lv], [e]):
      bb.stmts.add build(dst.st, Asgn(lv, e))
    of Store([t], [e0], [e1]):
      bb.stmts.add build(dst.st, Store(t, e0, e1))
    of Blit([e0], [e1], [e2]):
      bb.stmts.add build(dst.st, Blit(e0, e1, e2))
    of Clear([e0], [e1]):
      bb.stmts.add build(dst.st, Clear(e0, e1))
    of Call(pr, ...[e]):
      bb.stmts.add build(dst.st, Call(pr, ...e))
    of Call([t], [e0], ...[e1]):
      bb.stmts.add build(dst.st, Call(t, e0, ...e1))
    of Drop([e]):
      bb.stmts.add build(dst.st, Drop(e))
    of CheckedCall([t], [e0], ...[e1], tgt):
      commitBlock bbs, bb, build(dst.ex, CheckedCall(t, e0, ...e1, Goto(i(^(bbs.len+1))), ^target(tgt, map)))
      startBlock(bb)
    of CheckedCall(pr, ...[e], tgt):
      commitBlock bbs, bb, build(dst.ex, CheckedCall(pr, ...e, Goto(i(^(bbs.len+1))), ^target(tgt, map)))
      startBlock(bb)
    of CheckedCallAsgn(lo, [t], [e0], ...[e1], tgt):
      commitBlock bbs, bb, build(dst.ex, CheckedCallAsgn(lo, t, e0, ...e1, Goto(i(^(bbs.len+1))), ^target(tgt, map)))
      startBlock(bb)
    of CheckedCallAsgn(lo, pr, ...[e], tgt):
      commitBlock bbs, bb, build(dst.ex, CheckedCallAsgn(lo, pr, ...e, Goto(i(^(bbs.len+1))), ^target(tgt, map)))
      startBlock(bb)
    of Return():
      commitBlock bbs, bb, build(dst.ex, Return())
    of Return([e]):
      commitBlock bbs, bb, build(dst.ex, Return(e))
    of Raise([e], tgt):
      commitBlock bbs, bb, build(dst.ex, Raise(e, ^target(tgt, map)))
    of Branch([e], go0, go1):
      commitBlock bbs, bb, build(dst.ex, Branch(e, ^goto(go0, map), ^goto(go1, map)))
    of Unreachable():
      commitBlock bbs, bb, build(dst.ex, Unreachable())
    of Loop(i):
      commitBlock bbs, bb, build(dst.ex, Loop(i(^map[i.val])))

  proc scanStmt(ir: src.st, map: var Table[int64, int], wasJoin: var bool,
                next: var int) =
    match ir:
    of Stmts(...st):
      for it in st.items:
        scanStmt(it, map, wasJoin, next)
    of Join(i):
      if wasJoin:
        # merge joins immediately following each other
        map[i.val] = next - 1
      else:
        map[i.val] = next
        inc next
      wasJoin = false
    of Except(i, _):
      map[i.val] = next
      inc next
      wasJoin = false
    of CheckedCall(...any):
      inc next
      wasJoin = true
    of CheckedCallAsgn(...any):
      inc next
      wasJoin = true
    else:
      wasJoin = false

  proc decl(x: src.d): dst.d {.transform.} =
    case x
    of ProcDef([t], [p], [locs], st):
      var map: Table[int64, int]
      var wasJoin = false
      var next = 1
      scanStmt(st, map, wasJoin, next)
      var bbs: seq[dst.bb]
      var bb = BBlock(isExcept: false, params: p)
      blocks(st, bbs, bb, map)
      build ProcDef(t, locs, List(...bbs))

proc globalsToPointer(ir: L6, ptrsize: int): L5 {.pass.} =
  ## Turns global locations into pointer globals. Read access is turned
  ## into loads, write access into stores, and taking the address into copies
  ## of the pointer global.
  let (types, globals) = (;
    match ir:
    of Module(TypeDefs(...t), GlobalDefs(...d), ...any):
      var list = newSeq[src.t](d.len)
      for i, it in d.pairs:
        match it:
        of GlobalLoc(t, _): list[i] = t
        of GlobalDef(t, _): list[i] = t
        else:               unreachable()
      (t, list))

  proc gtype(g: Global): dst.t =
    globals[ord g] -> dst.t

  proc sizeAndAlignment(x: L6.t): tuple[size, align: Value[int64]] =
    match x:
    of tid:
      sizeAndAlignment(types[ord tid.val])
    of Union(i1, i2, ...any):  (i1, i2)
    of Record(i1, i2, ...any): (i1, i2)
    of Array(i1, i2, ...any):  (i1, i2)
    of Int(i):   (i, i)
    of UInt(i):  (i, i)
    of Float(i): (i, i)
    of Ptr():    (terminal int64(ptrsize), terminal int64(ptrsize))
    else:
      unreachable()

  proc expr(x: src.e): dst.e {.transform.} =
    case x
    of Copy(g):
      build Load(^gtype(g.val), Copy(g))
    of Addr(g):
      # the address of the location is now stored in the global
      build Copy(g)

  proc lvalue(x: src.lv): dst.lv {.transform.} =
    case x
    of g:
      build Deref(^gtype(g.val), Copy(g))

  proc stmt(x: src.st): dst.st {.transform.} =
    case x
    of Asgn(g, [e]):
      build Store(^gtype(g.val), Copy(g), e)

  proc decl(x: src.d): dst.d {.transform.} =
    case x
    of GlobalLoc(t, Data(_)):
      let (size, align) = sizeAndAlignment(t)
      build GlobalDef(Ptr(), Data(align, size))
    of GlobalLoc(t, Data(_, str)):
      let (_, align) = sizeAndAlignment(t)
      build GlobalDef(Ptr(), Data(align, str))

proc flattenPaths(ir: L5): L4 {.pass.} =
  ## Turns `At` and `Field` expressions into flat `Path` expressions, for easier
  ## processing by later passes.
  var locals: slice(src.t)
  let types = (;
    match ir:
    of Module(TypeDefs(...t), ...any): t)

  proc arrayElem(x: src.t): src.t =
    match x:
    of tid:
      arrayElem(types[ord tid.val])
    of Array(_, _, _, t):
      t
    else:
      unreachable()

  proc elemAt(x: src.t, i: int64): src.t =
    match x:
    of tid:
      elemAt(types[ord tid.val], i)
    of Record(_, _, ...f):
      match f[i]:
      of Field(_, t): t
    of Union(_, _, ...t):
      t[i]
    else:
      unreachable()

  proc filter(x: src.lv, args: var seq[dst.e]): (dst.ro, src.t) =
    match x:
    of Deref(t, [e]):
      (build(dst.ro, Deref(^(t -> dst.t), e)), t)
    of Field(lv, i):
      let (root, t) = filter(lv, args)
      args.add build(dst.e, i)
      (root, elemAt(t, i.val))
    of At(lv, [e]):
      let (root, t) = filter(lv, args)
      args.add e
      (root, arrayElem(t))
    of lo:
      (build(dst.ro, lo), locals[ord lo.val])

  proc typ(x: src.t): dst.t {.generated.}
  proc bblock(x: src.bb): dst.bb {.generated.}

  proc lvalue(x: src.lv): dst.lv {.transform.} =
    case x
    of lo: build lo
    of _:
      var args: seq[dst.e]
      let (root, t) = filter(x, args)
      assert args.len > 0
      build Path(^typ(t), root, ...args)

  proc decl(x: src.d): dst.d {.transform.} =
    case x
    of ProcDef([t], Locals(...t1), List(...bb)):
      locals = t1
      build ProcDef(t, Locals(...map(t1, typ)), List(...map(bb, bblock)))

proc aggregateParams(ir: L4): L3s2 {.pass.} =
  ## Turns all aggregate parameters into pointer parameters and replaces returns
  ## of aggregate with out parameters.

  # The pass' implementation is fairly involved. Only lvalue expressions can have
  # their address taken, meaning that rvalue argument expressions of aggregate
  # type have to be assigned to a temporary first, which then has its address
  # passed to the procedure.
  #
  # This leads to problem: an expression can have side effects, and reordering
  # it with other (impure) expressions might alter the program's meaning!
  #
  # Therefore, all (impure) expressions happening before an expression that is
  # turned into an assignment also have to be committed to temporaries. To
  # implement this, the operands of all operations are iterated from
  # *right to left*.
  proc resolve(types: slice(src.t), t: src.t): src.t =
    match t:
    of tid: types[ord tid.val]
    else:   t

  let (types, signatures) = (;
    match ir:
    of Module(TypeDefs(...t), _, ProcDefs(...d), ...any):
      var sigs = newSeq[src.t](d.len)
      for i, it in d.pairs:
        # the types for procedures are looked up, resolved, and cached, which
        # greatly speeds up later type lookup
        match it:
        of ProcDef(t1, ...any): sigs[i] = resolve(t, t1)
        of Import(t1, _):       sigs[i] = resolve(t, t1)
        else:                   unreachable()
      (t, sigs))

  var origLocals: slice(src.t)
  var locals: seq[dst.t]
  var params: PackedSet[Local]
  var stmts: seq[dst.st] ## accumulator for statements
  var needsSave: bool

  proc isAggregate(x: src.t): bool =
    match x:
    of tid: isAggregate(types[ord tid.val])
    of Record(...any): true
    of Array(...any): true
    of Union(...any): true
    else: false

  proc retType(x: src.t): src.t =
    match x:
    of tid:               retType(types[ord tid.val])
    of ProcTy(t, ...any): t
    else:                 unreachable()

  proc paramAt(x: src.t, pos: int): src.t =
    match x:
    of tid:
      paramAt(types[ord tid.val], pos)
    of ProcTy(_, ...t):
      t[pos]
    else: unreachable()

  proc newTemp(t: dst.t): dst.lo =
    result = terminal(Local(locals.len))
    locals.add(t)

  proc typ(x: src.t): dst.t {.transform.}
  proc expr(x: src.e): dst.e {.transform.}

  proc getType(x: src.e): dst.t =
    match x:
    of Le(_, _, _): build dst.t, UInt(i(1))
    of Lt(_, _, _): build dst.t, UInt(i(1))
    of Eq(_, _, _): build dst.t, UInt(i(1))
    of Not(_):      build dst.t, UInt(i(1))
    of Addr(_):     build dst.t, Ptr()
    of Nil():       build dst.t, Ptr()
    of Copy(g):     discard g; build dst.t, Ptr()
    of Copy(Path([t], ...any)): t
    of Copy(lo): locals[ord lo.val]
    of Call(pr, ...any): typ(retType(signatures[ord pr.val]))
    of Call(t, ...any):  typ(retType(t))
    of ProcVal(_):       build dst.t, Ptr()
    of i: discard i; unreachable()
    of fl: discard fl; unreachable()
    of e:
      match e:
      of any(t, ...any): typ(t)
      else:              unreachable()

  proc operand(x: src.e): dst.e =
    if needsSave:
      match x:
      of Addr([lv]): build dst.e, Addr(lv)
      of Nil():      build dst.e, Nil()
      of i: build dst.e, i
      of fl: build dst.e, fl
      else:
        let tmp = newTemp(getType(x))
        needsSave = false
        stmts.add build(dst.st, Asgn(tmp, ^expr(x)))
        needsSave = true
        build dst.e, Copy(tmp)
    else:
      expr(x)

  proc operands(x: slice(src.e)): seq[dst.e] =
    # process in reverse
    result.newSeq(x.len)
    result[^1] = expr(x[x.high])
    for i in countdown(x.high - 1, 0):
      result[i] = operand(x[i])

  proc lvalue(x: src.lv): dst.lv {.transform.} =
    case x
    of Path([t], ro, ...e):
      let e1 = operands(e)
      build Path(t, ^root(ro), ...e1)

  proc root(x: src.ro): dst.ro {.transform.} =
    case x
    of Deref([t], e):
      build Deref(t, ^operand(e))
    of lo:
      if lo.val in params:
        build Deref(^locals[ord lo.val], Copy(lo))
      else:
        build lo

  proc args(sig: src.t, e: slice(src.e)): seq[dst.e] =
    result = newSeq[dst.e](e.len)
    # process in reverse
    for i in countdown(e.high, 0):
      let it = e[i]
      let pt = paramAt(sig, i)
      if isAggregate(pt):
        let pt = typ(pt)
        let tmp = newTemp(pt)
        needsSave = false
        # ^^ the hoisted expression isn't affected by side effects
        match it:
        of Call(t, ...e1):
          stmts.add build(dst.st, Asgn(tmp, Call(^typ(t), ...args(t, e1))))
        of Call(pr, ...e1):
          stmts.add build(dst.st, Asgn(tmp, Call(pr, ...args(signatures[ord pr.val], e1))))
        else:
          stmts.add build(dst.st, Asgn(tmp, ^expr(it)))
        needsSave = true
        result[i] = build(dst.e, Addr(tmp))
      elif needsSave:
        let pt = typ(pt)
        let tmp = newTemp(pt)
        needsSave = false
        # ^^ the hoisted expression isn't affected by side effects
        stmts.add build(dst.st, Asgn(tmp, ^expr(it)))
        needsSave = true
        result[i] = build(dst.e, Copy(tmp))
      else:
        result[i] = expr(it)

  proc expr(x: src.e): dst.e {.transform.} =
    case x
    of Addr(lo):
      if lo.val in params:
        build Copy(lo)
      else:
        build Addr(lo)
    of Call(pr, ...e):
      let t = signatures[ord pr.val]
      let s = args(t, e)

      let rt = retType(t)
      if isAggregate(rt):
        let rt = typ(rt)
        let tmp = newTemp(rt)
        stmts.add build(dst.st, Call(pr, [...s, Addr(tmp)]))
        needsSave = true
        build Copy(tmp)
      else:
        build Call(pr, ...s)
    of Call(t, e0, ...e1):
      # note: e0 needs to be translated last, to keep the reverse processing order
      let s = args(t, e1)
      let rt = retType(t)
      if isAggregate(t):
        let rt = typ(rt)
        let tmp = newTemp(rt)
        stmts.add build(dst.st, Call(^typ(t), ^operand(e0), [...s, Addr(tmp)]))
        needsSave = true
        build Copy(tmp)
      else:
        build Call(^typ(t), ^operand(e0), ...s)
    of Copy(lo):
      if lo.val in params:
        build Load(^locals[ord lo.val], Copy(lo))
      else:
        build Copy(lo)

  proc stmt(x: src.st): dst.st {.transform.} =
    case x
    of Call(t, e0, ...e1):
      let args = args(t, e1)
      build Call(^typ(t), ^operand(e0), ...args)
    of Call(pr, ...e):
      build Call(pr, ...args(signatures[ord pr.val], e))
    of Blit(e0, e1, e2):
      let e2_1 = expr(e2)
      let e1_1 = operand(e1)
      let e0_1 = operand(e0)
      build Blit(e0_1, e1_1, e2_1)
    of Clear(e0, e1):
      let e1_1 = expr(e1)
      build Clear(^operand(e0), e1_1)

  var outParam: Option[Value[Local]]
  var delayed: Table[int64, dst.st]
  proc exit(x: src.ex): dst.ex {.transform.} =
    case x
    of CheckedCallAsgn(lo, t, e0, ...e1, Goto(i), [tgt]):
      let args = args(t, e1)
      let callee = operand(e0)
      if isAggregate(retType(t)):
        let tmp = newTemp(typ retType(t))
        # the temporary needs to be copied to the actual target upon landing
        delayed[i.val] = build(dst.st, Asgn(lo, Copy(tmp)))
        build CheckedCall(^typ(t), callee, [...args, Addr(tmp)], Goto(i), tgt)
      else:
        build CheckedCallAsgn(lo, ^typ(t), callee, ...args, Goto(i), tgt)
    of CheckedCallAsgn(lo, pr, ...e, Goto(i), [tgt]):
      let sig = signatures[ord pr.val]
      if isAggregate(retType(sig)):
        let tmp = newTemp(typ retType(sig))
        # the temporary needs to be copied to the actual target upon landing
        delayed[i.val] = build(dst.st, Asgn(lo, Copy(tmp)))
        build CheckedCall(pr, [...args(sig, e), Addr(tmp)], Goto(i), tgt)
      else:
        build CheckedCallAsgn(lo, pr, ...args(sig, e), Goto(i), tgt)
    of CheckedCall(pr, ...e, [go], [tgt]):
      build CheckedCall(pr, ...args(signatures[ord pr.val], e), go, tgt)
    of CheckedCall(t, e0, ...e1, [go], [tgt]):
      let args = args(t, e1)
      build CheckedCall(^typ(t), ^operand(e0), ...args, go, tgt)

  proc bblock(x: src.bb, pos: int): dst.bb {.transform.} =
    proc aux(lo: slice(src.lo), st0: slice(src.st), ex: src.ex,
             isExcept: bool, pos: int): dst.bb =
      # TODO: allow using child slices directly in expansion positions
      var bparams: seq[dst.lo]
      for it in lo.items:
        if pos == 0 and isAggregate(origLocals[ord it.val]):
          params.incl(it.val)
        bparams.add it

      if pos == 0 and outParam.isSome:
        bparams.add outParam.unsafeGet

      stmts.shrink(0)
      var extra: dst.st
      if delayed.pop(pos, extra):
        stmts.add extra

      for it in st0.items:
        needsSave = false
        let start = stmts.len
        let st = stmt(it)
        # the new statements, if any, were added in reverse; correct the order
        reverse(stmts.toOpenArray(start, stmts.high))
        stmts.add st

      needsSave = false

      let start = stmts.len
      let exit =
        if outParam.isSome:
          match ex:
          of Return([e0 -> e]):
            stmts.insert build(dst.st, Store(^getType(e0), Copy(^outParam.unsafeGet), e)), start
            build(dst.ex, Return())
          else:           exit(ex)
        else:             exit(ex)
      reverse(stmts.toOpenArray(start, stmts.high))

      if isExcept:
        build Except(Params(...bparams), ...stmts, exit)
      else:
        build Block(Params(...bparams), ...stmts, exit)

    case x
    of Block(Params(...lo), ...st, ex):
      aux(lo, st, ex, false, pos)
    of Except(Params(...lo), ...st, ex):
      aux(lo, st, ex, true, pos)

  proc typ(x: src.t): dst.t {.transform.} =
    case x
    of ProcTy(t0, ...t1):
      var got = newSeq[dst.t](t1.len)
      for i, it in t1.pairs:
        got[i] =
          if isAggregate(it): build Ptr()
          else:               typ(it)
      if isAggregate(t0):
        build ProcTy(Void(), [...got, Ptr()])
      else:
        build ProcTy(^typ(t0), ...got)

  proc decl(x: src.d): dst.d {.transform.} =
    case x
    of ProcDef(t0, Locals(...t1), List(...bb)):
      params.clear()
      delayed.clear()
      origLocals = t1
      locals = map(t1, typ)
      if isAggregate(retType(t0)):
        outParam = some newTemp(build(dst.t, Ptr()))
      else:
        outParam = none dst.lo
      var blocks = newSeq[dst.bb](bb.len)
      for i, it in bb.pairs:
        blocks[i] = bblock(it, i)
      # turn all aggregate parameter locals into pointers
      for it in params.items:
        locals[ord it] = build(dst.t, Ptr())
      build ProcDef(^typ(t0), Locals(...locals), List(...blocks))

proc aggregatesToBlob(ir: L3s2, ptrsize: uint): L3s1 {.pass.} =
  ## Turns all aggregate types into blob types. Path expression are turned into
  ## address value arithmetic.
  let types = (;
    match ir:
    of Module(TypeDefs(...t), ...any): t)
  var locals: slice(src.t)

  proc size(x: src.t): int64 =
    match x:
    of tid: size(types[ord tid.val])
    of Record(i, ...any): i.val
    of Union(i, ...any): i.val
    of Array(i, ...any): i.val
    of Int(i): i.val
    of UInt(i): i.val
    of Float(i): i.val
    of Ptr():      int64(ptrsize)
    else:                    unreachable()

  proc elementOffset(x: src.t, elem: int64): int64 =
    match x:
    of tid:
      elementOffset(types[ord tid.val], elem)
    of Record(_, _, ...f):
      match f[elem]:
      of Field(i, _): i.val
    of Union(...any):
      0
    of Array(_, _, _, t):
      size(t) * elem
    else:
      unreachable()

  proc typeOfElem(x: src.t, elem: int64): src.t =
    match x:
    of tid:
      typeOfElem(types[ord tid.val], elem)
    of Record(_, _, ...f):
      match f[elem]:
      of Field(_, t): t
    of Union(_, _, ...t):
      t[elem]
    of Array(_, _, _, t):
      t
    else:
      unreachable()

  proc typ(x: src.t): dst.t {.transform.} =
    case x
    of Record(i0, i1, ...any): build Blob(i0, i1)
    of Array(i0, i1, ...any): build Blob(i0, i1)
    of Union(i0, i1, ...any): build Blob(i0, i1)

  proc path(root: src.ro, elems: slice(src.e)): dst.e =
    var typ: src.t
    (typ, result) = (;
      match root:
      of Deref(t, [e]): (t, e)
      of lo:      (locals[ord lo.val], build(dst.e, Addr(lo))))

    var offset = 0'i64
    for it in elems.items:
      match it:
      of i:
        # a static field or array access
        offset += elementOffset(typ, i.val)
        typ = typeOfElem(typ, i.val)
      else:
        # an array access with a dynamic index
        if offset > 0:
          # add the static offset computed so far:
          result = build(dst.e, Offset(result, i(offset), i(1)))
          offset = 0

        typ = typeOfElem(typ, 0)
        # apply the dynamic array element offset:
        result = build(dst.e, Offset(result, ^expr(it), i(^size(typ))))

    if offset > 0:
      result = build(dst.e, Offset(result, i(offset), i(1)))

  proc lvalue(x: src.lv): dst.lv {.transform.} =
    case x
    of Path(...any): unreachable()

  proc expr(x: src.e): dst.e {.transform.} =
    case x
    of Copy(lv):
      match lv:
      of Path([t], ro, ...e):
        build Load(t, ^path(ro, e))
      else:
        build Copy(^lvalue(lv))
    of Addr(lv):
      match lv:
      of Path(_, ro, ...e):
        path(ro, e) # the path becomes an address value
      else:
        build Addr(^lvalue(lv))

  proc stmt(x: src.st): dst.st {.transform.} =
    case x
    of Asgn(lv, [e]):
      match lv:
      of Path([t], ro, ...e1):
        build Store(t, ^path(ro, e1), e)
      else:
        build Asgn(^lvalue(lv), e)

  proc bblock(x: src.bb): dst.bb {.generated.}

  proc decl(x: src.d): dst.d {.transform.} =
    case x
    of ProcDef([t], Locals(...t1), List(...bb)):
      locals = t1
      build ProcDef(t, Locals(...map(t1, typ)), List(...map(bb, bblock)))

proc localsToBlob(ir: L3s1, ptrSize: uint): L3 {.pass.} =
  ## Turns all non-blob locals that have their address taken into blob locals.
  let types = (;
    match ir:
    of Module(TypeDefs(...t), ...any): t)
  var marker: PackedSet[Local]
  var locals: seq[dst.t]

  proc scan(x: src.bb) =
    ## Scans the basic-block for address-of operations and registers all
    ## locals that have their address taken in marker.
    # this is terrible code, for the largest part consisting of just
    # traversal boilerplate. While generation of traversal logic would address
    # this issue, the code also exemplifies why having an AST with many
    # irregular forms is a bad idea
    proc scan(x: src.e) =
      match x:
      of Addr(lo):
        # the expression the pass is actually interested in
        marker.incl lo.val
      # traversal boilerplate follows
      of any(t, ...e): # call and binary operator forms
        discard t
        for it in e.items:
          scan(it)
      of Call(pr, ...e):
        discard pr
        for it in e.items:
          scan(it)
      of any(t0, t1, e): # the conversion forms
        discard t0; discard t1; scan(e)
      of any(...e):
        for it in e.items:
          scan(it)
      of any(t, e0, e1, lo): # the check forms
        discard t; discard lo; scan(e0); scan(e1)
      of Copy(_):    discard
      of ProcVal(_): discard
      of Nil():      discard
      of i:          discard i
      of fl:         discard fl

    proc scan(x: src.st) =
      # boilerplate...
      match x:
      of Call(_, ...e):
        for it in e.items:
          scan(it)
      of Asgn(_, e):
        scan(e)
      of Store(_, e0, e1):
        scan(e0); scan(e1)
      of any(...e):
        for it in e.items:
          scan(it)

    proc scan(x: src.ex) =
      # boilerplate...
      match x:
      of CheckedCallAsgn(_, _, ...e, _, _):
        for it in e.items:
          scan(it)
      of CheckedCall(_, ...e, _, _):
        for it in e.items:
          scan(it)
      of Raise(e, _):
        scan(e)
      of Branch(e, _, _):
        scan(e)
      of Return(e):
        scan(e)
      of Goto(_): discard
      of Loop(_): discard
      of any():   discard

    match x:
    of Block(_, ...st, ex):
      for it in st.items: scan(it)
      scan(ex)
    of Except(_, ...st, ex):
      for it in st.items: scan(it)
      scan(ex)

  proc sizeAndAlignment(x: src.t): (Value[int64], Value[int64]) =
    match x:
    of tid:      sizeAndAlignment(types[ord tid.val])
    of Int(i):   (i, i)
    of UInt(i):  (i, i)
    of Float(i): (i, i)
    of Ptr():    (terminal(int64(ptrSize)), terminal(int64(ptrSize)))
    else:        unreachable()

  proc isBlob(x: src.t): bool =
    match x:
    of tid:        isBlob(types[ord tid.val])
    of Blob(_, _): true
    else:            false

  proc typ(x: src.t): dst.t {.transform.} =
    case x

  proc expr(x: src.e): dst.e {.transform.} =
    case x
    of Copy(lo):
      if lo.val in marker:
        build Load(^locals[ord lo.val], Addr(lo))
      else:
        build Copy(lo)

  proc stmt(x: src.st): dst.st {.transform.} =
    case x
    of Asgn(lo, [e]):
      if lo.val in marker:
        build Store(^locals[ord lo.val], Addr(lo), e)
      else:
        build Asgn(lo, e)

  proc newTemp(t: dst.t): dst.lo =
    result = terminal Local(locals.len)
    locals.add t

  proc bblock(x: src.bb): dst.bb {.transform.} =
    proc update(x: src.lo, stmts: var seq[dst.st]): dst.lo =
      if x.val in marker:
        let typ = locals[ord x.val]
        let tmp = newTemp(typ)
        stmts.add build(dst.st, Store(typ, Addr(x), Copy(tmp)))
        tmp
      else:
        x

    # if a block parameter (which can only be of primitive type at this
    # point) has its address taken, the parameter must be turned back into a
    # primitive type. In effect, this means that the real parameter is copied
    # to a stack location on block entry that the rest of the procedure
    # then uses in place of the real parameter
    case x
    of Block(Params(...lo), ...[st], [ex]):
      var stmts: seq[dst.st]
      let params = mapIt(lo, update(it, stmts))
      build Block(Params(...params), [...stmts, ...st], ex)
    of Except(Params(...lo), ...[st], [ex]):
      var stmts: seq[dst.st]
      let params = mapIt(lo, update(it, stmts))
      build Except(Params(...params), [...stmts, ...st], ex)

  proc decl(x: src.d): dst.d {.transform.} =
    case x
    of ProcDef(t0, Locals(...t1), List(...bb)):
      marker.clear()
      locals = map(t1, typ)
      # gather the locals that have their address taken:
      for it in bb.items:
        scan(it)

      let bbs = map(bb, bblock)
      # ^^ potentially modifies the list of locals

      for i, it in t1.pairs:
        if Local(i) in marker and not isBlob(it):
          let (size, align) = sizeAndAlignment(it)
          locals[i] = build(dst.t, Blob(size, align))

      build ProcDef(^typ(t0), Locals(...locals), List(...bbs))

proc legalizeBlobOps(ir: L3): L2 {.pass.} =
  ## Turns loads, stores, and assignments of blob types into blit copies.
  let types = (;
    match ir:
    of Module(TypeDefs(...t), ...any): t
  )
  var locals: slice(src.t)

  proc size(x: src.t): int64 =
    match x:
    of Blob(i, _): i.val.int64
    of tid:        size(types[ord tid.val])
    else:          unreachable()

  proc isBlob(x: src.t): bool =
    match x:
    of Blob(...any): true
    of tid:          isBlob(types[ord tid.val])
    else:            false

  proc expr(x: src.e): dst.e {.generated.}
  proc typ(x: src.t): dst.t {.generated.}
  proc bblock(x: src.bb): dst.bb {.generated.}

  proc operand(x: src.e): dst.e =
    match x:
    of Copy([lv0 -> lv]):   build(dst.e, Addr(lv))
    of Load(_, [e]):        e
    else:                   unreachable()

  proc stmt(x: src.st): dst.st {.transform.} =
    case x
    of Store(t, [e0], e1):
      if isBlob(t):
        build Blit(e0, ^operand(e1), i(^size(t)))
      else:
        build Store(^typ(t), e0, ^expr(e1))
    of Asgn(lo, e):
      let t = locals[ord lo.val]
      if isBlob(t):
        build Blit(Addr(lo), ^operand(e), i(^size(t)))
      else:
        build Asgn(lo, ^expr(e))

  proc decl(x: src.d): dst.d {.transform.} =
    case x
    of ProcDef([t], Locals(...t1), List(...bb)):
      locals = t1
      build ProcDef(t, Locals(...map(t1, typ)), List(...map(bb, bblock)))

proc stackAlloc(ir: L2): L1 {.pass.} =
  ## Simple stack allocation pass. Adds a frame pointer local to all procedures
  ## that use stack memory and turns blob locals into stack locations.
  let types = (;
    match ir:
    of Module(TypeDefs(...t), ...any): t
  )
  var locals: seq[tuple[onStack: bool, offset: uint32]]
  var framePointer: dst.e

  func isBlob(x: src.t): bool =
    match x:
    of tid:        isBlob(types[ord tid.val])
    of Blob(_, _): true
    else:          false

  func sizeAndAlign(x: src.t): (uint32, uint32) =
    match x:
    of tid:          sizeAndAlign(types[ord tid.val])
    of Blob(i0, i1): (i0.val.uint32, i1.val.uint32)
    else:            unreachable()

  proc expr(x: src.e): dst.e {.transform.} =
    case x
    of Addr(lo):
      assert locals[ord lo.val].onStack, $ord(lo.val)
      if locals[ord lo.val].offset == 0:
        # no addition is necessary
        framePointer
      else:
        # XXX: it could make sense to try merging the offset computation into
        #      an enclosing one, where possible
        build Offset(framePointer, i(^locals[ord lo.val].offset), i(1))
    of Copy(lo):
      assert not locals[ord lo.val].onStack
      build Copy(lo(^locals[ord lo.val].offset))

  proc stmt(x: src.st): dst.st {.transform.} =
    case x
    of Asgn(lo, [e]):
      assert not locals[ord lo.val].onStack
      build Asgn(lo(^locals[ord lo.val].offset), e)

  proc exit(x: src.ex): dst.ex {.transform.} =
    case x
    of CheckedCallAsgn(lo, [t0 -> t], ...[e], [go], [tgt]):
      # XXX: very inefficient
      build CheckedCallAsgn(lo(^locals[ord lo.val].offset), t, ...e, go, tgt)
    of CheckedCallAsgn(lo, pr, ...[e], [go], [tgt]):
      build CheckedCallAsgn(lo(^locals[ord lo.val].offset), pr, ...e, go, tgt)

  proc bblock(x: src.bb): dst.bb {.generated.}

  proc typ(x: src.t): dst.t {.transform.} =
    case x
    of Blob(_, _): build Ptr()

  proc mapLocal(x: src.lo): dst.lo =
    assert not locals[ord x.val].onStack
    terminal Local(locals[ord x.val].offset)

  proc params(x: src.p): dst.p {.transform.} =
    case x
    of Params(...lo):
      var lo1 = newSeq[dst.lo](lo.len)
      for i, it in lo.pairs:
        lo1[i] = mapLocal(it)
      build Params(...lo1)

  proc decl(x: src.d): dst.d {.transform.} =
    case x
    of ProcDef(t, Locals(...t1), List(...bb)):
      locals.setLen(t1.len)
      var
        nextId = 0'u32
        stackOffset = 0'u32

      # assign a stack location to every blob local. At the moment, blob locals
      # are put into consecutive stack location, regardless of whether they have
      # disjoint lifetimes or not
      for i, it in t1.pairs:
        if isBlob(it):
          let (size, align) = sizeAndAlign(it)
          doAssert align <= 8, "over-aligned locals are currently not supported"
          # align the stack offset:
          stackOffset = (stackOffset + (align - 1)) and not (align - 1)
          locals[i] = (true, stackOffset)
          stackOffset += size # reserve the needed space
        else:
          locals[i] = (false, nextId)
          inc nextId

      # make the frame size a multiple of 8, so that the start of stack frame is
      # always on an 8 byte boundary
      stackOffset = (stackOffset + 7) and not 7'u32

      if stackOffset == 0:
        # the body stays as is, only the header needs to be modified
        build ProcDef(^typ(t), i(0), Locals(...map(t1, typ)), List(...map(bb, bblock)))
      else:
        framePointer = build(dst.e, Copy(lo(^Local(nextId))))
        var filtered = newSeq[dst.t](nextId + 1)
        for i, it in locals.pairs:
          if not it.onStack:
            filtered[it.offset] = typ(t1[i])

        filtered[^1] = build(dst.t, Ptr())

        var blocks = newSeq[dst.bb](bb.len)
        for i, it in bb.pairs:
          if i == 0:
            # pass the frame pointer as an extra argument
            match it:
            of Block(Params(...lo), ...[st], [ex]):
              blocks[i] = build(dst.bb, Block(Params([...map(lo, mapLocal), lo(nextid)]), ...st, ex))
            else:
              unreachable()
          else:
            blocks[i] = bblock(it)

        build ProcDef(^typ(t), i(stackOffset), Locals(...filtered), List(...blocks))

proc inlineTypes(ir: L1): LPtr {.pass.} =
  ## Removes `Blob` types and turns all identified numeric types into inline
  ## types.
  var types: Table[int, dst.t]

  proc typ(x: src.t): dst.t {.transform.} =
    case x
    of tid:
      var r: dst.t
      types.withValue ord(tid.val), val:
        r = val[]
      do:
        r = build tid
      r

  proc typedefs(x: src.td): dst.td {.transform.} =
    case x
    of TypeDefs(...t):
      var pos = 0
      # build the lookup table for types to inline:
      for i, it in t.pairs:
        match it:
        of ProcTy(...any):
          if pos != i:
            types[i] = build(dst.t, tid(pos)) # needs a fixup
          inc pos
        else:
          types[i] = typ(it)

      # inline the types and remove them from the list of typedefs:
      var outtypes = newSeq[dst.t](pos)
      pos = 0
      for it in t.items:
        match it:
        of ProcTy(...any):
          outtypes[pos] = typ(it)
          inc pos
        else:
          discard "drop the type"

      build TypeDefs(...outtypes)

proc ptrToInt(ir: LPtr, ptrsize: Positive): L0 {.pass.} =
  ## Turns pointer types into unsigned integers.
  proc typ(x: src.t): dst.t {.transform.} =
    case x
    of Ptr(): build UInt(i(ptrsize))

  proc expr(x: src.e): dst.e {.transform.} =
    case x
    of Nil(): build i(0) # represented as zero
    of Offset([e0], [e1], e2):
      match e2:
      of i:
        if i.val == 1:
          return build(Add(UInt(i(ptrsize)), e0, e1))
      else:
        discard "nothing to do"

      # the index is scaled
      build Add(UInt(i(ptrsize)), e0, Mul(UInt(i(ptrsize)), e1, ^expr(e2)))
    of Reinterp(Ptr(), UInt(i), [e0]):
      if i.val == 8: e0 # drop the bitcast
      else:          build Reinterp(UInt(i(ptrsize)), UInt(i), e0)
    of Reinterp(UInt(i), Ptr(), [e0]):
      if i.val == 8: e0 # drop the bitcast
      else:          build Reinterp(UInt(i), UInt(i(ptrsize)), e0)

# ----- compiler implementation ------

import experimental/[sexp, sexp_parse]
import passes/compilerdef
import std/[os, streams, strutils]

proc tryParse[T: Global or Proc or Local or Type](n: SexpNode, _: typedesc[T]): Option[T] =
  if n.kind == SList and n.len == 2 and n[0].kind == SSymbol and n[0].symbol == $T and n[1].kind == SInt:
    some(T(n[1].num))
  else:
    none(T)

proc tryParse(n: SexpNode, _: typedesc[string]): Option[string] =
  if n.kind == SString:
    some(n.str)
  elif n.kind == SList and n.len == 2 and n[0].kind == SSymbol and n[0].symbol == "StringVal" and n[1].kind == SString:
    some(n[1].str)
  else:
    none(string)

proc tryParse(n: SexpNode, _: typedesc[int64]): Option[int64] =
  if n.kind == SInt:
    some(int64(n.num))
  elif n.kind == SList and n.len == 2 and n[0].kind == SSymbol and n[0].symbol == "IntVal" and n[1].kind == SInt:
    some(int64(n[1].num))
  else:
    none(int64)

proc tryParse(n: SexpNode, _: typedesc[float]): Option[float] =
  if n.kind == SFloat:
    some(n.fnum)
  elif n.kind == SList and n.len == 2 and n[0].kind == SSymbol and n[0].symbol == "FloatVal":
    if n[1].kind == SFloat:
      some(n[1].fnum)
    elif n[1].kind == SSymbol:
      some(parseFloat(n[1].symbol))
    else:
      none(float)
  elif n.kind == SSymbol:
    some(parseFloat(n.symbol))
  else:
    none(float)

proc toSexp[T: Local or Global or Proc or Type](x: T): SexpNode =
  newSList([newSSymbol($T), newSInt(ord x)])

proc toSexp(x: int64): SexpNode =
  newSInt(int x)
proc toSexp(x: float): SexpNode =
  newSFloat(x)
proc toSexp(x: string): SexpNode =
  newSString(x)

proc parseInput(p: var SexpParser): Lskully.m {.parser.}
proc parseInner(p: var SexpParser): L0.m {.parser.}
proc render(p: L6.m): SexpNode {.unparser.}
proc render(p: L5.m): SexpNode {.unparser.}
proc render(p: L4.m): SexpNode {.unparser.}
proc render(p: L3s2.m): SexpNode {.unparser.}
proc render(p: L3.m): SexpNode {.unparser.}
proc render(p: L2.m): SexpNode {.unparser.}
proc render(p: L1.m): SexpNode {.unparser.}
proc render(p: LPtr.m): SexpNode {.unparser.}
proc render(p: L0.m): SexpNode {.unparser.}

let f = openFileStream(getExecArgs()[0], fmRead)
var p: SexpParser
p.open(f)
discard p.getTok()

let (ast, m) = parseInput(p)
f.close()
echo "parsed"

defineCompiler compile, LSkully, [
  basicBlocks,
  globalsToPointer(8),
  flattenPaths,
  aggregateParams,
  aggregatesToBlob(8),
  localsToBlob(8),
  legalizeBlobOps,
  stackAlloc,
  inlineTypes,
  ptrToInt(8)
]

discard compile(ast, m)
