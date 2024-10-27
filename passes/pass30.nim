## Lowers |L30| into the |L4| language. The pass needs to split the statements
## into basic-blocks (i.e., `Continuation`s). A basic-block is a sequence of
## statements with purely linear control-flow (i.e., no jumps, but non-raising
## calls are allowed).
##
## Locals need to be explicitly passed to continuation where they're used, and
## the pass uses a simple form of data-flow analysis to figure out along which
## edges what locals need to be passed.

import
  std/[intsets, tables],
  passes/[builders, changesets, trees, spec],
  vm/utils

type
  Node = TreeNode[NodeKind]

  TypeId = distinct uint32
  LocalId = distinct uint32
  BlockId = uint32 ## ID/index of a basic block

  Terminator = enum
    termNone ## uninitialized

    termGoto
    termLoop
    termRaise
    termPass # goto + pass value
    termUnreachable
    termBranch
    termSelect
    termCheckedCall
    termCheckedCallAsgn

  BBlock = object
    params: seq[LocalId]
      ## the locals passed to the block as parameters

    needs: PackedSet[LocalId]
      ## all locals the block needs access to
    has: PackedSet[LocalId]
      ## all locals available to the block

    isLoopStart: bool
      ## whether this block is the target of a loop back-edge
    hasIndirectAccess: bool
      ## whether there's a read or write through a pointer

    stmts: Slice[NodeIndex]

    term: Terminator
    outgoing: seq[int32] ## outgoing edges

  PassCtx = object
    types: NodeIndex

    # per-procedure state:
    locals: NodeIndex

    bblocks: seq[BBlock]
    blocks: seq[seq[tuple[blk: BlockId, edge: int32]]]
      ## a stack. For each enclosing entity that can be targeted by a
      ## ``Break``, the edges that require patching
    returns: seq[BlockId]
      ## all basic-blocks that end in a Return
    pinned: PackedSet[LocalId]
      ## locals that need to be pinned in memory (i.e., don't change location)

const
  IndirectAccess = {Copy, Clear, Store, Load, Call, CheckedCall,
                    CheckedCallAsgn}
    ## every operation that reads or writes through a pointer. Calls have to
    ## conservatively be treated as performing an indirect access.

# shorten some common procedure signatures:
using
  c: var PassCtx
  tree: PackedTree[NodeKind]
  n: NodeIndex
  changes: var ChangeSet[NodeKind]
  bu: var Builder[NodeKind]

proc `==`(a, b: LocalId): bool {.borrow.}
proc `<`(a, b: NodeIndex): bool {.borrow.}

func id(n: Node): LocalId {.inline.} =
  assert n.kind == Local
  LocalId(n.val)

func imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

func typ(n: Node): TypeId {.inline.} =
  assert n.kind == Type
  n.val.TypeId

func lookup(c: PassCtx; tree; typ: TypeId): NodeIndex =
  ## Returns the index of the type description for `typ`.
  tree.child(c.types, typ.int)

template localRef(id: uint32): Node =
  Node(kind: Local, val: id)

func returnType(c: PassCtx, tree; n): NodeIndex =
  assert tree[n].kind == ProcDef
  tree.child(c.lookup(tree, tree[n, 0].typ), 0)

func getType(c: PassCtx, tree; local: LocalId): TypeId =
  ## Returns the type ID for `local`.
  tree[c.locals, ord(local)].typ

proc scanUsages(c; tree; n) =
  # register all locals *used* within the sub-tree with the current BB:
  for it in tree.flat(n):
    if tree[it].kind in {Copy, At, Field, Addr} and tree[it, 0].kind == Local:
      c.bblocks[^1].needs.incl tree[it, 0].id
    elif tree[it].kind in IndirectAccess:
      c.bblocks[^1].hasIndirectAccess = true

proc startBlock(c; n; predecessor: BlockId) =
  c.bblocks[predecessor].outgoing.add c.bblocks.len.int32
  c.bblocks.add BBlock(stmts: n .. NodeIndex(0))

proc startBlock(c; n) =
  c.bblocks.add BBlock(stmts: n .. NodeIndex(0))

proc finishBlock(c; term: Terminator, n): BlockId =
  result = c.bblocks.high.BlockId
  c.bblocks[result].term = term
  c.bblocks[result].stmts.b = n

proc pushContext(c) =
  c.blocks.add @[]

proc popContext(c; n): bool =
  ## Pops the context for some structured control-flow construct. Returns
  ## 'true' when structured control-flow never leaves the construct, false
  ## otherwise.
  let exits = c.blocks.pop()
  result = exits.len == 0
  if not result:
    c.startBlock(n)
    for (bb, e) in exits.items:
      c.bblocks[bb].outgoing[e] = c.bblocks.high.int32

proc leave(c; frm: BlockId, blk: int) =
  ## Registers an edge between `frm` and the exit of `blk`.
  c.blocks[^blk].add (frm, c.bblocks[frm].outgoing.len.int32)
  c.bblocks[frm].outgoing.add 0

proc computeBlocks(c; tree; n): bool

proc computeBranch(c; tree; n) =
  if not c.computeBlocks(tree, n):
    c.leave(c.finishBlock(termGoto, tree.next(n)), 1)

proc computeBlocks(c; tree; n): bool =
  ## Computes the basic-block representation for statement `n`. Returns whether
  ## the trailing basic-block has a terminator already.
  case tree[n].kind
  of Unreachable:
    discard c.finishBlock(termUnreachable, n)
    result = true
  of Break:
    let prev = c.finishBlock(termGoto, n)
    c.leave(prev, tree[n, 0].imm.int + 1)
    result = true
  of Return:
    if tree.len(n) > 0:
      c.scanUsages(tree, tree.child(n, 0))
      c.returns.add c.finishBlock(termPass, n)
    else:
      c.returns.add c.finishBlock(termGoto, n)
    result = true
  of Raise:
    c.scanUsages(tree, tree.child(n, 0))
    discard c.finishBlock(termRaise, n)
    result = true
  of Asgn:
    let (dst, src) = tree.pair(n)
    c.scanUsages(tree, dst)
    c.scanUsages(tree, src)
    if tree[dst].kind == Local:
      let id = tree[dst].id
      if id in c.pinned:
        # SSA is disabled
        c.bblocks[^1].needs.incl id
      else:
        # use the SSA form for the local
        # TODO: an ``x = copy y`` should be turned into a goto + remapping. It'd
        #       result in more efficient code, possibly eliminating the copy
        let prev = c.finishBlock(termPass, n)
        c.startBlock(tree.next(n), prev)
        c.bblocks[^1].params.add id
  of CheckedCall:
    c.scanUsages(tree, n)
    let prev = c.finishBlock(termCheckedCall, n)
    c.startBlock(tree.next(n), prev)
  of CheckedCallAsgn:
    c.scanUsages(tree, n)
    let prev = c.finishBlock(termCheckedCallAsgn, n)
    c.startBlock(tree.next(n), prev)
    c.bblocks[^1].params.add tree[n, 0].id
  of Block:
    # not a terminator by itself
    c.pushContext()
    c.computeBranch(tree, tree.child(n, 0))
    result = c.popContext(tree.next(n))
  of Loop:
    # always create a new block, even if the current one is empty; it might
    # still be needed for spawning locals
    let prev = c.finishBlock(termGoto, n)
    c.startBlock(tree.child(n, 0), prev)
    let blk = c.bblocks.high.int32
    c.pushContext()
    if not c.computeBlocks(tree, tree.child(n, 0)):
      # add a back edge:
      c.bblocks[^1].outgoing.add blk
      c.bblocks[blk].isLoopStart = true
      discard c.finishBlock(termLoop, tree.next(n))

    result = c.popContext(tree.next(n))
  of If:
    c.scanUsages(tree, tree.child(n, 0))
    let blk = c.finishBlock(termBranch, n)
    c.pushContext()
    case tree.len(n)
    of 2: # if-then
      let (_, a) = tree.pair(n)
      c.startBlock(a, blk)
      c.computeBranch(tree, a)
      c.leave(blk, 1)
    of 3: # if-then-else
      let (_, a, b) = tree.triplet(n)
      c.startBlock(a, blk)
      c.computeBranch(tree, a)
      c.startBlock(b, blk)
      c.computeBranch(tree, b)
    else:
      unreachable()

    result = c.popContext(tree.next(n))
  of Case:
    c.scanUsages(tree, tree.child(n, 1))
    let blk = c.finishBlock(termSelect, n)
    c.pushContext()
    for it in tree.items(n, 2):
      let s = tree.child(it, 1)
      c.startBlock(s, blk)
      c.computeBranch(tree, s)
    result = c.popContext(tree.next(n))
  of Stmts:
    for i, it in tree.pairs(n):
      if c.computeBlocks(tree, it):
        assert i == tree.len(n) - 1, "unculled unreachable code detected"
        result = true
        break
  else:
    # just gather the usages of locals
    c.scanUsages(tree, n)

proc copyAndPatch(tree; n; locals: Table[LocalId, uint32],
                  bu): NodeIndex {.discardable.} =
  # XXX: due to the lack of stacked changesets/trees, we have to copy
  #      everything
  result = tree.next(n)

  var buf = newSeq[Node](ord(result) - ord(n))
  for i, node in buf.mpairs:
    let it = NodeIndex(ord(n) + i)
    if tree[it].kind == Local:
      node = localRef(locals[tree[it].id])
    else:
      node = tree[it]

  bu.add buf

proc translateStmt(tree; n; locals: Table[LocalId, uint32], bu): NodeIndex =
  case tree[n].kind
  of If, Case, Loop, Break, Raise, Return, Unreachable:
    unreachable()
  of Block, Stmts:
    # enter the block / statement list
    result = tree.child(n, 0)
  else:
    result = copyAndPatch(tree, n, locals, bu)

proc genList(c; src: Table[LocalId, uint32], bb: BBlock, edge: int, bu) =
  ## Emits the move-list for a ``Continue`` targeting `dst`.
  let dst = bb.outgoing[edge]
  bu.subTree List:
    if dst < c.bblocks.len: # ignore the exit continuation
      let
        dst = addr c.bblocks[dst]
        hasImplicit = bb.term == termPass or
                      (bb.term == termCheckedCallAsgn and edge == 0)

      for i in ord(hasImplicit)..<dst.params.len:
        # pinned locals must be renamed
        let op =
          if dst.params[i] in c.pinned: Rename
          else: Move
        bu.subTree op:
          bu.add localRef(src[dst.params[i]])

proc genContinue(c; src: Table[LocalId, uint32], bb: BBlock, edge: int, bu) =
  bu.subTree Continue:
    bu.add Node(kind: Immediate, val: bb.outgoing[edge].uint32)
    c.genList(src, bb, edge, bu)

proc genBlock(c; tree; bb: BBlock, bu) =
  ## Emits the code for the given basic block.
  var locals: Table[LocalId, uint32]

  bu.subTree Continuation:
    bu.subTree Params:
      for i, it in bb.params.pairs:
        bu.add Node(kind: Type, val: getType(c, tree, it).uint32)
        locals[it] = i.uint32

    bu.subTree Locals:
      # every local not passed via a block parameter needs to be spawned
      var i = bb.params.len
      for it in items(bb.needs - bb.has):
        bu.add Node(kind: Type, val: getType(c, tree, it).uint32)
        locals[it] = i.uint32 # add a mapping
        inc i

    block:
      # translate and emit all statements part of the block
      var n = bb.stmts.a
      while n < bb.stmts.b:
        n = translateStmt(tree, n, locals, bu)

    # generate and emit the exit:
    let last = bb.stmts.b
    case bb.term
    of termNone:
      unreachable()
    of termGoto:
      c.genContinue(locals, bb, 0, bu)
    of termLoop:
      bu.subTree Loop:
        bu.add Node(kind: Immediate, val: bb.outgoing[0].uint32)
        c.genList(locals, bb, 0, bu)
    of termRaise:
      bu.subTree Raise:
        copyAndPatch(tree, tree.child(last, 0), locals, bu)
        if bb.outgoing.len > 0:
          c.genContinue(locals, bb, 0, bu)
        else:
          bu.subTree Unwind: discard
    of termPass:
      bu.subTree Continue:
        bu.add Node(kind: Immediate, val: bb.outgoing[0].uint32)
        let e =
          case tree[last].kind
          of Asgn:   tree.child(last, 1)
          of Return: tree.child(last, 0)
          else:      unreachable()

        copyAndPatch(tree, e, locals, bu)
        c.genList(locals, bb, 0, bu)
    of termUnreachable:
      bu.subTree Unreachable: discard
    of termBranch:
      bu.subTree SelectBool:
        copyAndPatch(tree, tree.child(last, 0), locals, bu)
        c.genContinue(locals, bb, 1, bu) # if false
        c.genContinue(locals, bb, 0, bu) # if true
    of termSelect:
      bu.subTree Select:
        bu.copyFrom(tree, tree.child(last, 0)) # type
        copyAndPatch(tree, tree.child(last, 1), locals, bu) # selector
        var branch = tree.child(last, 2)
        for edge in 0..<bb.outgoing.len:
          bu.subTree Choice:
            bu.copyFrom(tree, tree.child(branch, 0))
            c.genContinue(locals, bb, edge, bu)
          branch = tree.next(branch)
    of termCheckedCall, termCheckedCallAsgn:
      bu.subTree CheckedCall:
        # ignore the destination local
        for it in tree.items(last, ord(bb.term == termCheckedCallAsgn)):
          copyAndPatch(tree, it, locals, bu)

        c.genContinue(locals, bb, 0, bu)
        if bb.outgoing.len > 1:
          c.genContinue(locals, bb, 1, bu)
        else:
          bu.subTree Unwind: discard

proc lowerProc(c: var PassCtx, tree; n; changes) =
  c.bblocks.setLen(0)
  c.returns.setLen(0)
  c.pinned.clear()

  c.locals = tree.child(n, 1)

  # disable the SSA from for all locals that need to be pinned in memory. Addr
  # operations can be nested, so don't use filter
  for it in tree.flat(tree.child(n, 2)):
    if tree[it].kind == Addr:
      var it = tree.child(it, 0)
      # skip paths:
      while tree[it].kind in {At, Field}:
        it = tree.child(it, 0)

      if tree[it].kind == Local:
        c.pinned.incl tree[it].id

  c.startBlock(tree.child(n, 2))
  # register all procedure parameters with the first block:
  for i in 1..<tree.len(c.lookup(tree, tree[n, 0].typ)):
    c.bblocks[0].params.add LocalId(i - 1)

  # the body of a procedure must always end with a terminator
  doAssert c.computeBlocks(tree, tree.child(n, 2)),
           "control-flow falls out of the body"
  assert c.blocks.len == 0

  block:
    var
      previous = -1
      i = 0

    # reaching definitions analysis: compute for every BB the set of available
    # locals (stored in the `has` set), which is a forward data-flow problem.
    # The BBs are sorted in reverse postorder (with the BBs with the back-edges
    # coming immediately after the other BBs part of the loop). There are also
    # no jumps to *within a loop*, meaning that a loop's entry BB dominates all
    # other BBs part of the loop. It follows that:
    # * after one iteration (in reverse postorder) over a loop's BBs:
    #   * the reaching definitions of the entry BB were propagated to all BBs
    #     in the loop
    #   * the reaching definitions from all within the loop are propagated to
    #     the back-edge (and thus the entry BB)
    # * after a second iteration, all reaching definitions from within the
    #   loop were propagated along every edge leaving the loop
    #
    # We therefore know that a loop must only ever be executed twice (at most).
    # BBs part of a block are visited 2 + N times, where N is the nesting
    # depth.
    while i < c.bblocks.len:
      let it = addr c.bblocks[i]

      for param in it.params.items:
        it.needs.excl param
        it.has.incl param

      for o in it.outgoing.items:
        c.bblocks[o].has.incl it.has
        if c.pinned.len > 0:
          # locals are spawned on first use (if not assigned to before); make
          # that information available to follow-up blocks, for pinned locals
          c.bblocks[o].has.incl it.needs * c.pinned

      if it.term == termLoop and i > previous:
        # found a not-yet followed back edge -> follow it
        previous = i
        i = it.outgoing[0]
      else:
        inc i # go to the next BB

    # handle pinned locals: mark them as live in every block where:
    # * they're available
    # * a read or write through a pointer happens
    if c.pinned.len > 0:
      for it in c.bblocks.mitems:
        if it.hasIndirectAccess:
          it.needs.incl c.pinned * it.has

    # liveness analysis: compute for every BB the set of locals live at the
    # start of it, which is a backward data-flow problem. Iterating over the
    # BB in postorder, given the CFG constraints listed above, it follows that:
    # * after one iteration over a loop, the live set for the entry BB is
    #   correct
    # * after a second iteration, the live set for the loop's other BBs is
    #   correct too
    # Note that instead of following loops eagerly (like in the forward pass),
    # they need to be followed outermost to innermost (i.e., the outermost
    # loop has to complete a full iteration before any of its nested loops are
    # repeated)
    var
      looping = false
      entry = 0

    previous = c.bblocks.len # set to something greater than any valid BB index
    i = c.bblocks.high

    while i >= 0:
      let it = addr c.bblocks[i]

      if not looping and i < previous and it.term == termLoop:
        previous = i
        looping = true # don't repeat nested loops
        entry = it.outgoing[0] # the entry BB of the loop

      # all locals live in outgoing blocks and of which a definition reaches
      # here are also live in the current block
      for o in it.outgoing.items:
        it.needs.incl c.bblocks[o].needs * c.bblocks[o].has

      # exclude the parameters again
      for param in it.params.items:
        it.needs.excl param

      if looping and entry == i:
        # entry of the loop reached -> follow the back-edge (in reverse)
        looping = false # now repeat nested loops
        i = previous
      else:
        dec i

  # fill-in the parameters:
  for it in c.bblocks.mitems:
    for x in items(it.needs * it.has):
      it.params.add x

  # patch all return edges. Do this after the has/needs propagation
  for it in c.returns.mitems:
    c.bblocks[it].outgoing.add c.bblocks.len.int32

  changes.remove(tree, n, 1) # remove the list of locals
  changes.replace(tree.child(n, 2), Continuations):
    for it in c.bblocks.items:
      c.genBlock(tree, it, bu)

    if c.returns.len > 0:
      # append the exit continuation
      bu.subTree Continuation:
        bu.subTree Params:
          let typ = returnType(c, tree, n)
          if tree[typ].kind != Void:
            bu.add tree[typ]

proc lower*(tree): Changeset[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = PassCtx(types: tree.child(0))

  for it in tree.items(tree.child(2)):
    c.lowerProc(tree, it, result)
