## Turns all aggregate parameters into pointer parameters and replaces returns
## of aggregate with out parameters (|L4| -> |L3|).

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

import
  std/[intsets, tables],
  passes/[changesets, syntax, trees],
  vm/utils

type
  Node = TreeNode[NodeKind]
  LocalId = distinct uint32
  TypeId = uint32

  Context = object
    addrType: Node
    cache: seq[NodeIndex]
      ## indexed by procedure IDs. Caches the signature type for every
      ## procedure. This greatly speeds up type computation of calls, as it
      ## eliminates the tree traversal necessary for seeking to the procdef

    # per-procedure state:
    locals: NodeIndex
    stmts: seq[VirtualTree]
      ## statements to be appendend before the currently processed statement,
      ## stored in reverse
    temps: seq[Node]
      ## new temporaries allocated for the procedure
    firstTemp: int
      ## the ID offset for the first temporary
    delayed: Table[uint32, VirtualTree]
      ## maps BB indices to the assignments to emit at their start, if any

    outParam: Node
      ## the local holding the out parameter
    hasOutParam: bool
    params: PackedSet[LocalId]
      ## the parameters that are turned into pointers

using
  c: var Context
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var ChangeSet[NodeKind]

proc imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

proc local(n: Node): LocalId =
  assert n.kind == Local
  LocalId(n.val)

proc isAggregate(tree; n: Node): bool =
  var n = n
  if n.kind == Type:
    # resolve the indirection:
    n = tree[tree.child(0), n.val]
  n.kind in {Record, Union, Array}

proc signature(c; tree; n): NodeIndex =
  case tree[n].kind
  of Type: tree.child(tree.child(0), tree[n].val)
  of Proc: c.cache[tree[n].val]
  else:    unreachable()

proc typeof(c; tree; n): Node =
  case tree[n].kind
  of Path, Load, Deref, Add, Sub, Mul, Div, Mod, BitNot, BitAnd, BitOr, BitXor,
     AddChck, SubChck, MulChck, Shl, Shr, Conv, Reinterp, Neg:
    # these are all expression that store their result type as the first
    # node
    tree[n, 0]
  of Not, Eq, Lt, Le:
    # boolean expressions
    Node(kind: UInt, val: 1)
  of Copy:
    c.typeof(tree, tree.child(n, 0))
  of Local:
    tree[c.locals, tree[n].val]
  of Call:
    # fetch the return type from the callee's signature
    tree[c.signature(tree, tree.child(n, 0)), 0]
  of Global:
    # fetch the type from the ``GlobalDef``
    tree[tree.child(tree.child(1), tree[n].val), 0]
  else:
    unreachable()

proc newLocal(c; typ: Node): Node =
  assert typ.kind in {Type, UInt, Int, Float}
  result = Node(kind: Local, val: uint32(c.firstTemp + c.temps.len))
  c.temps.add typ

proc newAddrExpr(bu; local: Node): VirtualTree =
  bu.buildTree tree(Addr, node(local))

proc newCopyExpr(bu; local: Node): VirtualTree =
  bu.buildTree tree(Copy, node(local))

template addStmt(c: var Context, body: untyped) =
  ## Adds the tree evaluated to by `body` to the statement list, but before
  ## any statements added from within `body`.
  let i = c.stmts.len
  c.stmts.setLen(i + 1)
  let tmp = body
  # don't assign `body` to `stmts` directly, as it'd cause memory corruption due
  # to stale references...
  c.stmts[i] = tmp

proc lowerExpr(c; tree; n; bu)
proc lowerOperand(c; tree; n; reference: int, bu)

proc lowerPath(c; tree; n; reference: int, bu) =
  # a path itself cannot be hoisted, but its operands can be (and have to be)
  case tree[n].kind
  of Path:
    # process in reverse
    for i in countdown(tree.len(n) - 1, 2):
      if tree[n, i].kind != Immediate:
        c.lowerOperand(tree, tree.child(n, i), reference, bu)

    let root = tree.child(n, 1)
    if tree[root].kind == Deref:
        c.lowerOperand(tree, tree.child(root, 1), reference, bu)
    elif tree[root].kind == Local and  tree[root].local in c.params:
      # (Path typ x ...) -> (Path typ (Deref typ' x) ...)
      bu.replace root:
        bu.buildTree:
          tree(Deref,
            node(c.typeof(tree, root)),
            tree(Copy, node(tree[root])))

  of Local, Global:
    discard "nothing to do"
  else:
    unreachable()

proc lowerAddr(c; tree; n; reference: int, bu) =
  if tree[n, 0].kind == Local and tree[n, 0].local in c.params:
    # the parameter stores an address value already, turn the Addr into Copy
    bu.replace n, bu.newCopyExpr(tree[n, 0])
  else:
    c.lowerPath(tree, tree.child(n, 0), reference, bu)

proc loweredExpr(c; tree; n; bu): VirtualTree =
  bu.openTree(tree, n, c.lowerExpr(tree, n, bu))

proc lowerOperand(c; tree; n; reference: int, bu) =
  if reference != c.stmts.len:
    # code was reordered, the operand's value must be materialized to a
    # temporary. Except for some leaf expressions, always assign the expression
    # to a temporary, even if it is pure (and thus unaffected by any reordering
    # of side-effectful code). This is simpler, but it also results in worse
    # code and/or more work for later passes (more locals usually equals more
    # work and bookkeeping).
    case tree[n].kind
    of IntVal, FloatVal, ProcVal:
      discard "nothing to do"
    of Addr:
      c.lowerAddr(tree, n, reference, bu)
    else:
      let tmp = c.newLocal(c.typeof(tree, n))
      c.addStmt:
        bu.buildTree tree(Asgn, node(tmp), embed(c.loweredExpr(tree, n, bu)))
      bu.replace n, bu.newCopyExpr(tmp)
  else:
    c.lowerExpr(tree, n, bu)

proc lowerCallArgs(c; tree; n; start: int, last: BackwardsIndex; bu) =
  let sig = c.signature(tree, tree.child(n, start))
  assert tree[sig].kind == ProcTy
  let reference = c.stmts.len

  # don't consider the dynamic callee value, if any, during the loop, as it's
  # not part of the signature
  let first =
    if tree[n, start].kind == Type:
      start + 2
    else:
      start + 1

  for i in countdown(tree.len(n) - last.int, first):
    let arg = tree.child(n, i)
    if isAggregate(tree, tree[sig, i - first + 1]):
      let local = c.newLocal(tree[sig, i - first + 1])
      if tree[arg].kind == Call:
        c.addStmt bu.openTree(tree, arg, m) do:
          c.lowerCallArgs(tree, arg, 0, ^1, bu)
          bu.insert m, tree.fin(arg), bu.newAddrExpr(local)
      else:
        # non-call expressions of aggregate type always use a temporary, even
        # if the expression is an l-value (which could have its address taken
        # directly). This is because we don't know whether this is the last
        # use of the l-value, and thus whether a potential mutation of the
        # parameter would be oberservable where it should not be
        c.addStmt bu.buildTree do:
          tree(Asgn, node(local), embed(c.loweredExpr(tree, arg, bu)))

      bu.replace arg, bu.newAddrExpr(local)
    else:
      c.lowerOperand(tree, arg, reference, bu)

  # now process the callee operand, if one exists
  if tree[n, start].kind == Type:
    c.lowerOperand(tree, tree.child(n, start + 1), reference, bu)

proc lowerExpr(c; tree; n, bu) =
  case tree[n].kind
  of IntVal, FloatVal, ProcVal:
    discard "nothing to do"
  of Copy:
    let x = tree.child(n, 0)
    if tree[x].kind == Local and tree[x].local in c.params:
      # (Copy local) -> (Load typ (Copy local))
      bu.replace n,
        bu.buildTree tree(Load, node(c.typeof(tree, x)), embed(n))
    else:
      c.lowerPath(tree, x, c.stmts.len, bu)
  of Addr:
    c.lowerAddr(tree, n, c.stmts.len, bu)
  of Not:
    c.lowerExpr(tree, tree.child(n, 0), bu)
  of Load, Neg, BitNot:
    c.lowerExpr(tree, tree.child(n, 1), bu)
  of Reinterp, Conv:
    c.lowerExpr(tree, tree.child(n, 2), bu)
  of Add, Sub, Mul, Div, Mod, BitAnd, BitOr, BitXor, AddChck, SubChck, MulChck,
     Eq, Lt, Le, Shl, Shr:
    let (_, a, b) = tree.triplet(n)
    let reference = c.stmts.len
    c.lowerExpr(tree, b, bu)
    c.lowerOperand(tree, a, reference, bu)
  of Call:
    # only non-aggregate-returning calls can reach here
    c.lowerCallArgs(tree, n, 0, ^1, bu)
  else:
    unreachable()

proc lowerCall(c; tree; n; dest: VirtualTree, bu) =
  ## (Call a b ...) -> (Call a' b' ... dest)
  c.addStmt bu.openTree(tree, n, m) do:
    c.lowerCallArgs(tree, n, 0, ^1, bu)
    bu.insert m, tree.fin(n), dest

proc lowerStmt(c; tree; n; bu) =
  let reference = c.stmts.len
  case tree[n].kind
  of Asgn:
    let (a, b) = tree.pair(n)
    if tree[b].kind == Call and isAggregate(tree, c.typeof(tree, a)):
      # (Asgn x (Call a b ...)) ->
      #   (Call a' b' ... (Addr tmp)) (Asgn x' (Copy tmp))
      let local = c.newLocal(c.typeof(tree, a))
      c.lowerCall(tree, b, bu.newAddrExpr(local), bu)
      c.lowerPath(tree, a, reference, bu)
      bu.replace b, bu.newCopyExpr(local)
    else:
      c.lowerExpr(tree, b, bu)
      c.lowerPath(tree, a, reference, bu)
  of Store:
    let (typ, a, b) = tree.triplet(n)
    if tree[b].kind == Call and isAggregate(tree, tree[typ]):
      # (Store typ x (Call a b ...)) ->
      #   (Call a' b' ... (Addr tmp)) (Store typ x' (Copy tmp))
      let local = c.newLocal(tree[typ])
      c.lowerCall(tree, b, bu.newAddrExpr(local), bu)
      c.lowerOperand(tree, a, reference, bu)
      bu.replace b, bu.newCopyExpr(local)
    else:
      c.lowerExpr(tree, b, bu)
      c.lowerOperand(tree, a, reference, bu)
  of Call:
    c.lowerCallArgs(tree, n, 0, ^1, bu)
  of Blit:
    let (a, b, s) = tree.triplet(n)
    c.lowerExpr(tree, s, bu)
    c.lowerOperand(tree, b, reference, bu)
    c.lowerOperand(tree, a, reference, bu)
  of Clear:
    let (a, b) = tree.pair(n)
    c.lowerExpr(tree, b, bu)
    c.lowerOperand(tree, a, reference, bu)
  of Drop:
    c.lowerExpr(tree, tree.child(n, 0), bu)
  else:
    unreachable()

proc lowerTerminator(c; tree; n; bu) =
  case tree[n].kind
  of CheckedCall:
    c.lowerCallArgs(tree, n, 0, ^3, bu)
  of CheckedCallAsgn:
    let dest = tree.child(n, 0)
    if isAggregate(tree, c.typeof(tree, dest)):
      # (CheckedCallAsgn dst ...) -> (CheckedCall ... (Addr tmp) ...)
      let local = c.newLocal(c.typeof(tree, dest))
      let target = tree.child(n, ^2)
      bu.modifyTree tree, n, CheckedCall, m:
        bu.remove m, dest
        c.lowerCallArgs(tree, n, 1, ^3, bu)
        bu.insert m, target, bu.newAddrExpr(local)
      # the temporary is copied to the actual destination on entry of
      # the non-error BB
      c.delayed[tree[target, 0].imm] = bu.buildTree:
        tree(Asgn, node(tree[dest]), tree(Copy, node(local)))
    else:
      c.lowerCallArgs(tree, n, 1, ^3, bu)
  of Return:
    if tree.len(n) > 0:
      let val = tree.child(n, 0)
      if c.hasOutParam:
        if tree[val].kind == Call:
          # optimization: don't introduce a temporary, re-use the out parameter
          c.lowerCall(tree, val, bu.newCopyExpr(c.outParam), bu)
        else:
          # (Return x) -> (Store typ out x') (Return)
          c.addStmt bu.buildTree do:
            tree(Store,
              node(c.typeof(tree, val)),
              tree(Copy, node(c.outParam)),
              embed(c.loweredExpr(tree, val, bu)))

        bu.modifyTree tree, n, m:
          bu.remove m, val
      else:
        c.lowerExpr(tree, val, bu)
  of Branch, Raise:
    c.lowerExpr(tree, tree.child(n, 0), bu)
  of Select:
    c.lowerExpr(tree, tree.child(n, 1), bu)
  of Unreachable, Goto, Loop:
    discard "nothing to do"
  else:
    unreachable()

proc addStmts(c; tree; m: var TreeRef, at: NodeIndex, bu) =
  for i in countdown(c.stmts.high, 0):
    bu.insert m, at, c.stmts[i]
  c.stmts.shrink(0)

proc lowerProc(c; tree; n; sig: NodeIndex, bu) =
  c.temps.shrink(0)
  c.params.clear()

  let (_, locals, blocks) = tree.triplet(n)
  c.locals = locals
  c.firstTemp = tree.len(locals)

  if isAggregate(tree, tree[sig, 0]):
    c.hasOutParam = true
    c.outParam = c.newLocal(c.addrType)
  else:
    c.hasOutParam = false

  # gather the set of parameters that need to be turned into pointers
  block:
    let x = tree.child(blocks, 0)
    for i, it in tree.pairs(tree.child(x, 0)):
      if isAggregate(tree, tree[sig, i + 1]):
        c.params.incl tree[it].local

  for i, blk in tree.pairs(blocks):
    bu.modifyTree tree, blk, stmts:
      if c.hasOutParam and i == 0:
        # add the out parameter to the entry block:
        bu.modifyTree tree, tree.child(blk, 0), m:
          bu.insert m, tree.fin(tree.child(blk, 0)), c.outParam

      # insert the follow-up assignment for a preceding checked calls,
      # if any:
      var asgn: VirtualTree
      if c.delayed.pop(i.uint32, asgn):
        bu.insert stmts, tree.child(blk, 1), asgn

      for s in tree.items(blk, 1, ^2): # go over all statements
        c.lowerStmt(tree, s, bu)
        c.addStmts(tree, stmts, s, bu)

      c.lowerTerminator(tree, tree.last(blk), bu)
      c.addStmts(tree, stmts, tree.last(blk), bu)

  # all delayed assignments must have been popped from the table
  assert c.delayed.len == 0

  if c.temps.len > 0 or c.params.len > 0:
    bu.modifyTree tree, c.locals, list:
      # update the parameter locals:
      for it in c.params.items:
        bu.replace tree.child(c.locals, it.ord), c.addrType

      # append the new locals to the list of locals:
      let last = tree.fin(c.locals)
      for it in c.temps.items:
        bu.insert list, last, it

proc lower*(tree; ptrSize: int): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of a pointer value.
  var c = Context(addrType: Node(kind: UInt, val: ptrSize.uint32))

  for it in tree.items(tree.child(0)):
    if tree[it].kind == ProcTy:
      result.modifyTree tree, it, m:
        # turn an aggregate return value into an out parameter:
        if isAggregate(tree, tree[it, 0]):
          result.replace tree.child(it, 0), result.buildTree(tree(Void))
          result.insert m, tree.fin(it), c.addrType

        for x in tree.items(it, 1):
          if isAggregate(tree, tree[x]):
            result.replace x, c.addrType

  let procs = tree.child(2)

  # cache the signature type for each procedure:
  c.cache.newSeq(tree.len(procs))
  for i, it in tree.pairs(procs):
    c.cache[i] = tree.child(tree.child(0), tree[it, 0].val.int)

  # lower the procedures:
  for i, it in tree.pairs(procs):
    if tree[it].kind == ProcDef:
      c.lowerProc(tree, it, c.cache[i], result)
