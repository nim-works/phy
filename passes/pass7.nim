## Lowers |L7| into the |L4| language. The pass needs to split the statements
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

    termOther
    termLoop
    termPass # goto + pass value
    termCheckedCall
    termCheckedCallAsgn

  BlockFlag = enum
    bfIndirectAccess ## an indirect memory access happens within the block
    bfExcept         ## the block is entry point of an exception handler

  BBlock = object
    params: seq[LocalId]
      ## the locals passed to the block as parameters

    needs: PackedSet[LocalId]
      ## all locals the block needs access to
    has: PackedSet[LocalId]
      ## all locals available to the block

    isLoopStart: bool
      ## whether this block is the target of a loop back-edge
    flags: set[BlockFlag]

    term: Terminator
    outgoing: seq[int32] ## outgoing edges

    stmts: Slice[NodeIndex]
      ## the statements part of the basic block. Needed for the
      ## translation

  PassCtx = object
    types: NodeIndex

    # per-procedure state:
    locals, conts: NodeIndex

    bblocks: seq[BBlock]
    map: Table[uint32, int32]
      ## maps labels of the input language to their corresponding basic-block
      ## index
    returns: seq[int]
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

func getType(c: PassCtx, tree; local: LocalId): TypeId =
  ## Returns the type ID for `local`.
  tree[c.locals, ord(local)].typ

func returnType(c: PassCtx, tree; n): NodeIndex =
  assert tree[n].kind == ProcDef
  tree.child(c.lookup(tree, tree[n, 0].typ), 0)

proc scanUsages(tree; n; bb: var BBlock) =
  # register all locals *used* within the sub-tree with the current BB:
  for it in tree.flat(n):
    if tree[it].kind in {Copy, At, Field, Addr} and tree[it, 0].kind == Local:
      bb.needs.incl tree[it, 0].id
    elif tree[it].kind in IndirectAccess:
      bb.flags.incl bfIndirectAccess

template current(c): BBlock =
  c.bblocks[^1]

proc close(c; n; term = termOther) =
  c.current.term = term
  c.current.stmts.b = n

proc start(c; n) =
  if c.bblocks[^1].term == termNone:
    # the previous BB isn't finished yet
    if c.bblocks[^1].stmts.a != n or c.bblocks[^1].params.len > 0:
      # the current BB has parameters, or is non empty; cannot merge. Close it
      # first and then start a new one
      c.current.outgoing.add c.bblocks.len.int32
      c.close(n)
      c.bblocks.add BBlock(stmts: n .. n)
    else:
      # don't add a new BB; merge with the previous one. This prevents
      # unnecessary blocks for, e.g.:
      #   (Join 0)
      #   (Join 1)
      c.current.stmts.a = n
  else:
    c.bblocks.add BBlock(stmts: n .. n)


proc addEdge(bb: var BBlock, label: uint32) =
  bb.outgoing.add -int32(label + 1)

proc scanStmt(c; tree; n) =
  ## Scans the statement at `n` for usages of locals. Gathering the basic
  ## blocks and the control-flow edges between them is also handled here.

  proc addExcEdge(bb: var BBlock; tree; n) {.nimcall.} =
    if tree[n].kind != Unwind:
      bb.addEdge tree[n, 0].imm

  case tree[n].kind
  of Unreachable:
    c.close(n)
  of Continue:
    c.current.addEdge tree[n, 0].imm
    c.close(n)
  of Loop:
    c.current.addEdge tree[n, 0].imm
    c.close(n, termLoop)
  of Return:
    if tree.len(n) == 1: # return with value
      scanUsages(tree, tree.child(n, 0), c.current)
    c.close(n)
    c.returns.add c.bblocks.high # needs to be patched later
  of Raise:
    c.current.addExcEdge(tree, tree.child(n, 1))
    # a raise exit also passes along a value
    c.close(n, termPass)
  of CheckedCall:
    scanUsages(tree, n, c.current)
    c.current.outgoing.add c.bblocks.len.int32
    c.current.addExcEdge(tree, tree.child(n, ^1))
    c.close(n, termCheckedCall)
    c.start(tree.next(n))
  of CheckedCallAsgn:
    scanUsages(tree, n, c.current)
    c.current.outgoing.add c.bblocks.len.int32
    c.current.addExcEdge(tree, tree.child(n, ^1))
    c.close(n, termCheckedCallAsgn)
    c.start(tree.next(n))
    c.current.params.add tree[n, 0].id
  of SelectBool:
    let (x, els, then) = tree.triplet(n)
    scanUsages(tree, x, c.current)
    c.current.addEdge tree[els, 0].imm
    c.current.addEdge tree[then, 0].imm
    c.close(n)
  of Select:
    scanUsages(tree, tree.child(n, 1), c.current)
    for it in tree.items(n, 2):
      c.current.addEdge tree[tree.last(it), 0].imm

    c.close(n)
  of Join:
    c.start(n)
    c.map[tree[n, 0].imm] = c.bblocks.high.int32
  of Except:
    assert c.current.term != termNone, "execution falls through to `Except`"
    c.start(tree.next(n))
    c.map[tree[n, 0].imm] = c.bblocks.high.int32
    c.current.params.add tree[n, 1].id
    c.current.flags.incl bfExcept
  of Asgn:
    # if possible, a split is introduced at assignments
    let (dst, src) = tree.pair(n)
    scanUsages(tree, dst, c.current)
    scanUsages(tree, src, c.current)
    if tree[dst].kind == Local:
      let id = tree[dst].id
      if id in c.pinned:
        # SSA is disabled
        c.current.needs.incl id
      else:
        # use the SSA form for the local
        c.current.outgoing.add c.bblocks.len.int32
        c.close(n, termPass)
        c.start(tree.next(n))
        c.current.params.add id
  else:
    # just gather the usages of locals
    scanUsages(tree, n, c.current)

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

proc genList(c; src: Table[LocalId, uint32], bb: BBlock, edge: int, bu) =
  ## Emits the move-list for a ``Continue`` targeting `dst`.
  let dst = bb.outgoing[edge]
  bu.subTree List:
    if dst < c.bblocks.len: # ignore the exit continuation
      let
        dst = addr c.bblocks[dst]
        # some exits have an implicit argument
        hasImplicit = bb.term in {termPass, termCheckedCallAsgn} or
                      (bb.term == termCheckedCall and edge == 1)

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
  bu.subTree (if bfExcept in bb.flags: Except else: Continuation):
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
      while ord(n) < ord(bb.stmts.b):
        if tree[n].kind != Join:
          copyAndPatch(tree, n, locals, bu)
        n = tree.next(n)

    let n = bb.stmts.b
    case tree[n].kind
    of Unreachable:
      bu.subTree Unreachable:
        discard
    of Continue, Join:
      # a join functions like a continue here
      c.genContinue(locals, bb, 0, bu)
    of Loop:
      bu.subTree Loop:
        bu.add Node(kind: Immediate, val: bb.outgoing[0].uint32)
        c.genList(locals, bb, 0, bu)
    of Return:
      if tree.len(n) == 0:
        c.genContinue(locals, bb, 0, bu)
      else:
        bu.subTree Continue:
          bu.add Node(kind: Immediate, val: bb.outgoing[0].uint32)
          copyAndPatch(tree, tree.child(n, 0), locals, bu)
          c.genList(locals, bb, 0, bu)
    of Raise:
      bu.subTree Raise:
        copyAndPatch(tree, tree.child(n, 0), locals, bu)
        if bb.outgoing.len == 0:
          bu.subTree Unwind:
            discard
        else:
          c.genContinue(locals, bb, 0, bu)
    of SelectBool:
      bu.subTree SelectBool:
        copyAndPatch(tree, tree.child(n, 0), locals, bu)
        c.genContinue(locals, bb, 0, bu)
        c.genContinue(locals, bb, 1, bu)
    of Select:
      bu.subTree Select:
        bu.copyFrom(tree, tree.child(n, 0))
        copyAndPatch(tree, tree.child(n, 1), locals, bu)
        for it in tree.items(n, 2):
          bu.subTree Choice:
            bu.copyFrom(tree, tree.child(it, 0))
            c.genContinue(locals, bb, 0, bu)
    of Asgn:
      bu.subTree Continue:
        bu.add Node(kind: Immediate, val: bb.outgoing[0].uint32)
        copyAndPatch(tree, tree.child(n, 1), locals, bu)
        c.genList(locals, bb, 0, bu)
    of CheckedCallAsgn, CheckedCall:
      bu.subTree CheckedCall:
        for it in tree.items(n, ord(tree[n].kind == CheckedCallAsgn), ^2):
          copyAndPatch(tree, it, locals, bu)

        c.genContinue(locals, bb, 0, bu)
        if bb.outgoing.len == 2:
          c.genContinue(locals, bb, 1, bu)
        else:
          bu.subTree Unwind:
            discard
    else:
      unreachable()

proc lowerProc(c: var PassCtx, tree; n; changes) =
  c.bblocks.shrink(0)
  c.returns.shrink(0)
  c.pinned.clear()
  c.map.clear()

  c.locals = tree.child(n, 1)
  c.conts = tree.child(n, 2)

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

  # add the entry basic block and register all procedure parameters with it:
  c.bblocks.add BBlock(stmts: tree.child(c.conts, 0) .. c.conts)
  for i in 1..<tree.len(c.lookup(tree, tree[n, 0].typ)):
    c.bblocks[0].params.add LocalId(i - 1)

  # scan the body:
  for it in tree.items(c.conts):
    c.scanStmt(tree, it)

  assert c.current.term != termNone,
         "body doesn't end in control-flow statement"

  # correct the outgoing edges of blocks, now that we know the label-to-block
  # mappings
  for i, bb in c.bblocks.mpairs:
    for it in bb.outgoing.mitems:
      if it < 0:
        it = c.map[uint32(-(it + 1))]

      # a loop must be backward control-flow, all other control-flow must be
      # facing forward
      assert it <= i == (bb.term == termLoop), "illegal control-flow"

    # also mark the basic-blocks at the start of a loop:
    if bb.term == termLoop:
      c.bblocks[bb.outgoing[0]].isLoopStart = true

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
        if bfIndirectAccess in it.flags:
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
  for it in c.returns.items:
    c.bblocks[it].outgoing.add c.bblocks.len.int32

  changes.remove(tree, n, 1) # remove the list of locals
  changes.replace(c.conts, Continuations):
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
