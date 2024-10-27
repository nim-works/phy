## Lowers |L1| code into |L0| code. This means hoisting the basic-block locals
## into the procedure header. Block parameters and arguments are removed in the
## process.
##
## The implementation currently uses a simple forward register allocation
## scheme. No copy elision is performed, and no effort is made to prevent
## copies on block edges.

import
  std/[tables],
  passes/[changesets, spec, trees],
  vm/[utils]

type
  Node = TreeNode[NodeKind]
  TypeId = distinct uint32
  BlockId = uint32 # exists for documentation purposes
  Register = uint32 # exists for documentation purposes

  PassCtx = object
    ## Per-procedure context. Shared between procedures to prevent
    ## reallocations.
    blockIdx: NodeIndex
      ## the node index of the currently processed block

    registers: seq[tuple[typ: TypeId, free: bool]]
      ## all registers allocated for the procedure
    params: Table[BlockId, seq[Register]]
      ## maps block IDs to the registers their parameters occupy
      ## XXX: this is an inefficient data structure

    numParams: int
      ## per-block state. the number of parameters the current block has
    map: seq[Register]
      ## per-block state. Maps a block parameter/local to a register

using
  c: var PassCtx
  tree: PackedTree[NodeKind]
  bu: var Cursor[NodeKind]
  n: NodeIndex

func typ(n: Node): TypeId =
  assert n.kind == Type
  n.val.TypeId

func id(n: Node): uint32 =
  n.val

proc imm(x: Node): uint32 =
  x.val

func toIndex(c: PassCtx, tree; n): int =
  ## Translates a ``Param`` or ``Local`` node to an index to access `c.map`
  ## with.
  if tree[n].kind == Param:
    tree[n].id.int
  else:
    c.numParams + tree[n].id.int

func getType(c: PassCtx, tree; n): TypeId =
  ## Returns the type ID for the parameter or local.
  let idx = if tree[n].kind == Param: 0 else: 1
  tree[tree.child(tree.child(c.blockIdx, idx), tree[n].id)].typ

proc alloc(c; typ: TypeId): uint32 =
  for i, it in c.registers.pairs:
    if it.free and it.typ.ord == typ.ord:
      return i.uint32

  # create a new register:
  c.registers.add (typ, false)
  result = c.registers.high.uint32

proc interpret(c; tree; n) =
  ## Interprets expression/statement `n` and updates the register allocator
  ## state accordingly.
  for it in tree.filter(n, {Move, Asgn}):
    let idx = c.toIndex(tree, tree.child(it, 0))
    case tree[it].kind
    of Move:
      # a move marks the last use of a local/parameter. Free the occupied
      # register
      c.registers[c.map[idx]].free = true
    of Asgn:
      interpret(c, tree, tree.child(n, 1)) # recurse a single time
      # the assignment happens *after* usages in the RHS. Allocate a register
      # for the local
      c.map[idx] = c.alloc(c.getType(tree, tree.child(it, 0)))
    else:
      unreachable()

proc interpretExit(c; tree; n) =
  c.interpret(tree, n) # interpret the statement as usual
  # checked-call assignments need special handling for the assignment:
  if tree[n].kind == CheckedCallAsgn:
    let x = tree.child(n, 0)
    c.map[c.toIndex(tree, x)] = c.alloc(c.getType(tree, x))

proc lowerUsages(c; tree; bu) =
  bu.filterTree tree, {Local, Param}:
    bu.replace tree, Node(kind: Local, val: c.map[c.toIndex(tree, bu.pos)])

proc handleBlockArgs(c; tree; bu) =
  ## Assigns registers to the block parameters of the targetted blocks, injecting
  ## assignments when necessary. The
  let n = bu.pos
  if tree[n].kind in {Goto, Loop} and tree[n, 0].imm in c.params:
    # all critical edges were split, meaning that we only need to handle
    # argument/parameter mismatch for single outgoing edges
    # FIXME: ``Raise`` edges also need to be handled here
    let params = addr c.params[tree[n, 0].imm]

    # watch out! if any registers on the outgoing edge are part of the target
    # block's parameters, the assignment order is significant
    var moves: seq[tuple[src, dst, tmp: Register]]

    for i, it in tree.pairs(tree.child(n, 1)):
      let id = c.toIndex(tree, it)
      let formal = params[i]
      if formal != c.map[id]:
        # a move is needed
        if c.registers[formal].free:
          # can move directly
          moves.add (c.map[id], formal, formal)
          c.registers[formal].free = false
        else:
          # needs a temporary
          moves.add (c.map[id], formal, c.alloc(c.registers[formal].typ))

    # XXX: the way temporaries are used works, but it is very inefficient

    if moves.len > 0:
      # first move into the temporaries (which might be the final destination
      # already), then move from the temporaries to the destinations
      for it in moves.items:
        bu.subTree Asgn:
          bu.add Node(kind: Local, val: it.tmp)
          bu.subTree Move:
            bu.add Node(kind: Local, val: it.src)

        c.registers[it.dst].free = false

      for it in moves.items:
        if it.tmp != it.dst:
          bu.subTree Asgn:
            bu.add Node(kind: Local, val: it.dst)
            bu.subTree Move:
              bu.add Node(kind: Local, val: it.tmp)

          c.registers[it.dst].free = false

      # note: it's important that there are no register "leaks" here
  else:
    # set the physical registers for the target block's parameters
    for exit in tree.filter(n, {Goto}):
      var o: seq[uint32]
      for i, it in tree.pairs(tree.child(exit, 1)):
        o.add c.map[tree[it].id]

      c.params[tree[exit, 0].imm] = o

proc lowerExit(c; tree; bu) =
  case tree[bu.pos].kind
  of Goto, Loop:
    # remove the list of block arguments:
    bu.keepTree tree:
      bu.keep(tree)
      bu.skip(tree)
  else:
    bu.filterTree tree, {Goto, Local, Param}:
      if tree[bu.pos].kind in {Local, Param}:
        # update usages:
        bu.replace tree, Node(kind: Local, val: c.map[c.toIndex(tree, bu.pos)])
      else:
        c.lowerExit(tree, bu)

proc lowerProc(c; tree; bu) =
  c.registers.shrink(0)
  c.params.clear()

  var locals: int
  bu.keepTree tree:
    bu.keep(tree) # keep the type
    bu.keep(tree) # keep the stack space specifier
    locals = bu.addLater() # the locals are added later
    # lower the blocks:
    var idx = 0
    bu.forEach tree, n:
      c.blockIdx = n
      bu.keepTree tree: # basic block
        # block parameter handling:
        c.numParams = tree.len(tree.child(n, 0))
        c.map.setLen(c.numParams + tree.len(tree.child(n, 1)))

        if c.numParams > 0:
          if idx == 0:
            # this is the entry block and it has parameters. By convention,
            # these parameters must occupy the first registers in the procedure
            for x, it in tree.pairs(tree.child(n, 0)):
              c.map[x] = c.alloc(tree[it].typ)
          else:
            # inherit the parameter -> phyiscal mappings
            for x, reg in c.params[BlockId idx].pairs:
              c.registers[reg].free = false
              c.map[x] = reg

        if tree[n].kind == Except:
          # replace the parameter list with an single local. Allocate it and correct
          # the parameter mappings
          let tmp = c.alloc(tree[tree.child(n, 0), 0].typ)
          c.map.insert(tmp, 0)
          bu.replace tree, Node(kind: Local, val: tmp)
        else:
          # replace with an empty parameter list
          bu.replace tree, Node(kind: Params)

        bu.skip(tree) # remove the list of locals

        # assign registers to the locals based on their usage:
        for i in 2..<tree.len(n)-1:
          c.interpret(tree, tree.child(n, i))
        c.interpretExit(tree, tree.last(n))

        # update all usages of locals in statements:
        for _ in 2..<tree.len(n)-1:
          c.lowerUsages(tree, bu)

        c.handleBlockArgs(tree, bu)
        c.lowerExit(tree, bu)

        # reset the register state. All registers must be free at the start of
        # processing a basic block,
        for reg in c.map.items:
          c.registers[reg].free = true

      inc idx

  bu.complete locals, Locals:
    for it in c.registers.items:
      bu.add Node(kind: Type, val: it.typ.uint32)

proc lower*(tree): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = PassCtx()

  var bu = initCursor[NodeKind](tree)
  bu.keep(tree)
  bu.keep(tree)
  bu.forEach tree, n:
    c.lowerProc(tree, bu)

  result = toChangeset(bu)
