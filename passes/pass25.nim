## A pass that turns the transforms the bodies of procedures into the
## basic-block-oriented structure (|L25| -> |L5|).

import
  std/[tables],
  passes/[builders, changesets, trees, syntax],
  vm/utils

type
  Node = TreeNode[NodeKind]

  LocalId = distinct uint32
  BlockId = int32 ## ID/index of a basic block

  Terminator = enum
    termNone ## uninitialized

    termOther
    termLoop
    termPass # goto + pass value
    termCheckedCall
    termCheckedCallAsgn

  BlockFlag = enum
    bfExcept         ## the block is entry point of an exception handler

  BBlock = object
    params: seq[LocalId]
      ## the locals passed to the block as parameters

    flags: set[BlockFlag]

    term: Terminator
    outgoing: seq[BlockId] ## outgoing edges

    stmts: Slice[NodeIndex]
      ## the statements part of the basic block. Needed for the
      ## translation

  PassCtx = object
    bblocks: seq[BBlock]
    map: Table[uint32, BlockId]
      ## maps labels of the input language to their corresponding basic-block
      ## index

# shorten some common procedure signatures:
using
  c: var PassCtx
  tree: PackedTree[NodeKind]
  n: NodeIndex
  changes: var ChangeSet[NodeKind]
  bu: var Builder[NodeKind]

func id(n: Node): LocalId {.inline.} =
  assert n.kind == Local
  LocalId(n.val)

func imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

template current(c): BBlock =
  c.bblocks[^1]

proc close(c; n; term = termOther) =
  c.current.term = term
  c.current.stmts.b = n

proc start(c; n) =
  if c.bblocks[^1].term == termNone:
    # the previous BB isn't finished yet
    if c.bblocks.len == 1 or c.bblocks[^1].stmts.a != n or
       c.bblocks[^1].params.len > 0:
      # the current BB is the entry BB, has parameters, or is non empty; cannot
      # merge. Close it first and then start a new one
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
  ## Gathers which basic blocks exist and where, as well as the control-flow
  ## edges between the blocks.

  proc addExcEdge(bb: var BBlock; tree; n) {.nimcall.} =
    if tree[n].kind != Unwind:
      bb.addEdge tree[n, 0].imm

  case tree[n].kind
  of Unreachable:
    c.close(n)
  of Goto:
    c.current.addEdge tree[n, 0].imm
    c.close(n)
  of Loop:
    c.current.addEdge tree[n, 0].imm
    c.close(n, termLoop)
  of Return:
    c.close(n)
  of Raise:
    c.current.addExcEdge(tree, tree.child(n, 1))
    # a raise exit also passes along a value
    c.close(n, termPass)
  of CheckedCall:
    c.current.outgoing.add c.bblocks.len.int32
    c.current.addExcEdge(tree, tree.child(n, ^1))
    c.close(n, termCheckedCall)
    c.start(tree.next(n))
  of CheckedCallAsgn:
    c.current.outgoing.add c.bblocks.len.int32
    c.current.addExcEdge(tree, tree.child(n, ^1))
    c.close(n, termCheckedCallAsgn)
    c.start(tree.next(n))
  of Branch:
    let (_, els, then) = tree.triplet(n)
    c.current.addEdge tree[els, 0].imm
    c.current.addEdge tree[then, 0].imm
    c.close(n)
  of Select:
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
  else:
    discard "nothing to do"

proc genGoto(c; bb: BBlock, edge: int, bu) =
  bu.subTree Goto:
    bu.add Node(kind: Immediate, val: bb.outgoing[edge].uint32)

proc genErrorExit(c; bb: BBlock, edge: int, bu) =
  if edge < bb.outgoing.len:
    c.genGoto(bb, edge, bu)
  else:
    # use the unwind target when there's no handler within the current
    # procedure
    bu.subTree Unwind: discard

proc genBlock(c; tree; bb: BBlock, bu) =
  ## Emits the code for the given basic block.
  bu.subTree (if bfExcept in bb.flags: Except else: Block):
    bu.subTree Params:
      for i, it in bb.params.pairs:
        bu.add Node(kind: Local, val: it.uint32)

    block:
      # copy all statements except for joins into the block
      var n = bb.stmts.a
      while ord(n) < ord(bb.stmts.b):
        if tree[n].kind != Join:
          bu.copyFrom(tree, n)
        n = tree.next(n)

    let n = bb.stmts.b
    case tree[n].kind
    of Unreachable:
      bu.subTree Unreachable:
        discard
    of Goto, Join:
      # a join functions like a continue here
      c.genGoto(bb, 0, bu)
    of Loop:
      bu.subTree Loop:
        bu.add Node(kind: Immediate, val: bb.outgoing[0].uint32)
    of Return:
      bu.subTree Return:
        if tree.len(n) == 1:
          bu.copyFrom(tree, tree.child(n, 0))
    of Raise:
      bu.subTree Raise:
        bu.copyFrom(tree, tree.child(n, 0))
        c.genErrorExit(bb, 0, bu)
    of Branch:
      bu.subTree Branch:
        bu.copyFrom(tree, tree.child(n, 0))
        c.genGoto(bb, 0, bu)
        c.genGoto(bb, 1, bu)
    of Select:
      var edge = 0
      bu.subTree Select:
        bu.copyFrom(tree, tree.child(n, 0))
        bu.copyFrom(tree, tree.child(n, 1))
        for it in tree.items(n, 2):
          bu.subTree Choice:
            bu.copyFrom(tree, tree.child(it, 0))
            c.genGoto(bb, edge, bu)
          inc edge
    of CheckedCallAsgn, CheckedCall:
      bu.subTree tree[n].kind:
        for it in tree.items(n, 0, ^2):
          bu.copyFrom(tree, it)

        c.genGoto(bb, 0, bu)
        c.genErrorExit(bb, 1, bu)
    else:
      unreachable()

proc lowerProc(c: var PassCtx, tree; n; changes) =
  c.bblocks.shrink(0)
  c.map.clear()

  let
    (_, params, locals) = tree.triplet(n)
    body = tree.next(locals)

  # add the entry BB:
  c.bblocks.add BBlock(stmts: tree.child(body, 0) .. body)
  for it in tree.items(params):
    c.bblocks[0].params.add tree[it].id

  # scan the body:
  for it in tree.items(body):
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

  changes.modifyTree tree, n, m:
    changes.remove m, params
    changes.replace body, List:
      for it in c.bblocks.items:
        c.genBlock(tree, it, bu)

proc lower*(tree): Changeset[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = PassCtx()

  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      c.lowerProc(tree, it, result)
