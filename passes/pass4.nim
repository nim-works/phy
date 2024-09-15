## Lowers |L4| into the |L3| language. The lowering is, for the most part,
## concerned with assigning procedure-wide locals (registers) to continuation
## locals.
##
## **What we get:**
## * a directed cyclic graph
##   * nodes represent continuation locals
##   * edges represent moves
##   * edges are in pre-order
## * constraints requiring some nodes to share the same register
##
## **What we want:**
## * each node having a register assigned
## * locals within a continuation to all have a different register assigned
## * (good to have) as little total registers as possible
## * (good to have) as little copies as possible
##
## **How we get there:**
## 1. compute "islands" of nodes, using a simple, linear time graph
##    coloring scheme
## 2. all nodes part of an island share the same register
## 3. two different islands *may* share the same register, but only if both
##    are never part of the same continuation
## 4. rewrite the code, injecting assignments (i.e. copies) for all edges
##    where the source and destination register differs
##
## The graph being able to contain cycles is irrelevant for the algorithm,
## thanks to the pre-established order.

# XXX: consider splitting this pass into two:
#      * one that does the register allocation and mapping and figuring out
#        where copies are needed
#      * one that injects the new continuations and rewrites checked calls
#      This would reduce complexity, at the cost of (likely) being less run-
#      time efficient

import
  std/[intsets, tables],
  passes/[builders, changesets, trees, spec]

type
  TypeId = distinct uint32
  Node = TreeNode[NodeKind]

  IndexRange = Slice[int32]

  Edge = object
    ## Edge in a directed graph. Corresponds to a ``Move`` or ``Rename``.
    src, dst: uint32
    noCopy: bool

  EdgeGroup = object
    ## Groups a sequence of edges together. Corresponds to a ``Continue`` or
    ## ``Loop``.
    n: NodeIndex
    target: uint32
    edges: IndexRange ## index range into the `edges` sequence
    needsCopy: bool

  GraphNode = tuple
    ## Corresponds to a ``Continuation`` parameter or local.
    keep: bool
    color: uint32

  Cont = object
    n: NodeIndex
    numParams: int32
    nodes: IndexRange  ## index range into the `nodes` sequence
    groups: IndexRange ## index range into the `groups` sequence

  Graph = object
    conts: seq[Cont]
    groups: seq[EdgeGroup]
    edges: seq[Edge]
    nodes: seq[GraphNode]

  Register = uint32 ## ID of a register

  PassCtx = object
    types: NodeIndex

    # per-procedure state:
    conts: NodeIndex
    locals: seq[tuple[typ: TypeId, free: bool]]
      ## all allocated registers
    nodeToReg: seq[Register]
      ## maps every node to a register
    contMap: seq[uint32]
      ## maps continuations to their new ID. Empty, if no patching is needed

    temps: Table[int32, Register]
      ## node -> intermediate temporary to assign to first
      ## XXX: this is a massive hack. The table is only needed for the duration
      ##      of on a ``lowerCont`` call, yet it's stored in the pass' context

# shorten some common procedure signatures:
using
  c: var PassCtx
  gr: Graph
  tree: PackedTree[NodeKind]
  n: NodeIndex
  changes: var ChangeSet[NodeKind]

proc `==`(a, b: TypeId): bool {.borrow.}

func id(n: Node): uint32 {.inline.} =
  assert n.kind == Local, $n.kind
  n.val

func imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

func typ(n: Node): TypeId {.inline.} =
  assert n.kind == Type
  n.val.TypeId

func lookup(c: PassCtx; tree; typ: TypeId): NodeIndex =
  ## Returns the index of the type description for `typ`.
  tree.child(c.types, typ.int)

func len(tree; n; c: int): int =
  tree.len(tree.child(n, c))

func addUnique[T](s: var seq[T], it: T) {.inline.} =
  if it notin s:
    s.add it

template localRef(id: uint32): Node =
  Node(kind: Local, val: id)

iterator ritems[T](s: seq[T]): lent T =
  for i in countdown(s.high, 0):
    yield s[i]

proc buildGraph(tree; n): Graph =
  ## Builds the assignment graph from the list of continuations at `n`.

  proc slice(start, len: int): Slice[int32] =
    int32(start) .. int32(start + len - 1)

  # setup the ``Cont`` list and the nodes:
  var numNodes = 0
  for it in tree.items(n):
    if tree.len(it) > 1:
      let
        numParams = tree.len(it, 0)
        s = slice(numNodes, numParams + tree.len(it, 1))
      result.conts.add Cont(n: it, nodes: s, numParams: int32 numParams)
      numNodes = s.b + 1
    else:
      result.conts.add Cont(n: it, nodes: slice(0, 0)) # an empty Cont

  result.nodes.newSeq(numNodes)

  for cont in result.conts.mitems:
    # go over all exits and register an edge group for each:
    cont.groups.a = result.groups.len.int32
    for g in tree.filter(tree.last(cont.n), {Continue, Loop}):
      let
        target   = tree[g, 0].imm
        list     = tree.child(g, ^1)
        numEdges = tree.len(list)

      result.groups.add:
        EdgeGroup(n: g, target: target,
                  edges: slice(result.edges.len, numEdges))

      # implicit arguments are passed to the first parameter, but don't have
      # an edge in the graph; handle this case by shifting the start
      let start = result.conts[target].nodes.a +
                  (result.conts[target].numParams - numEdges)

      # register an edge for every entry in the list:
      for off, e in tree.pairs(list):
        result.edges.add:
          Edge(src: cont.nodes.a.uint32 + tree[e, 0].id,
               dst: uint32(start + off),
               noCopy: tree[e].kind == Rename)

    cont.groups.b = result.groups.high.int32

proc colorGraph(gr: var Graph) =
  ## Assigns a color to every node in the graph.
  var
    next    = 1'u32
    markers = newSeq[PackedSet[uint32]](gr.conts.len)
      ## for each node group (i.e., continuation) the already seen colors.
      ## Used to prevent invalid color propagation

  # pre-color nodes pairs that are forced to share the same register:
  for g in gr.groups.items:
    for e in gr.edges.toOpenArray(g.edges.a, g.edges.b).items:
      if e.noCopy:
        if gr.nodes[e.src].color == 0:
          gr.nodes[e.src] = (true, next)
          inc next

        let color = gr.nodes[e.src].color
        if gr.nodes[e.dst].color != color:
          # TODO: use proper error reporting
          doAssert gr.nodes[e.dst].color == 0, "cannot satisfy constraints"
          doAssert not containsOrIncl(markers[g.target], color),
                   "cannot satisfy constraints"
          gr.nodes[e.dst] = (true, color)

  # assign unique colors to the rest:
  for n in gr.nodes.mitems:
    if n.color == 0:
      n.color = next
      inc next

  # the graph is now colored correctly, but allocating registers would
  # result in rather inefficient code; coalesce first

  proc mark(nodes: var seq[GraphNode], s: var PackedSet[uint32],
            a, b: uint32) {.nimcall.} =
    let color = nodes[a].color
    # don't propagate a color if it would introduce a duplicate
    if not nodes[b].keep and not s.containsOrIncl(color):
      # mark the node as having its final color
      nodes[b] = (true, color)

  # propagate colors forward:
  for g in gr.groups.items:
    for e in gr.edges.toOpenArray(g.edges.a, g.edges.b).items:
      mark(gr.nodes, markers[g.target], e.src, e.dst)

  reset markers # free the memory already

  # propagate colors backward:
  for cont in gr.conts.ritems:
    var marker: PackedSet[uint32]

    for it in cont.nodes.items:
      marker.incl gr.nodes[it].color

    for g in gr.groups.toOpenArray(cont.groups.a, cont.groups.b):
      for e in gr.edges.toOpenArray(g.edges.a, g.edges.b).items:
        mark(gr.nodes, marker, e.dst, e.src)

proc alloc(c; typ: TypeId): Register =
  ## Returns a free register and marks it occupied.
  for i, it in c.locals.mpairs:
    if it.free and it.typ == typ:
      it.free = false
      return i.Register

  result = c.locals.len.Register
  c.locals.add (typ, false)

proc insertCopies(c; tree; gr; g: EdgeGroup, at: int, exit: NodeKind, changes) =
  ## Inserts the copies for the edge group `g`. `at` is the index of the
  ## continuation where the new continuation is to be inserted.
  let arity = gr.conts[g.target].numParams
  var copies: seq[tuple[src, dst, tmp: Register]]
  var active = newSeq[uint32](arity)

  # gather the set of input registers and mark them occupied:
  for i, it in gr.edges.toOpenArray(g.edges.a, g.edges.b).pairs:
    active[i] = c.nodeToReg[it.src]
    c.locals[active[i]].free = false # mark as occupied

  # gather the output registers and produce the list of copy operations:
  for i, it in gr.edges.toOpenArray(g.edges.a, g.edges.b).pairs:
    let reg = c.nodeToReg[it.dst]
    if active[i] != reg:
      # requires a copy
      if c.locals[reg].free:
        # okay, can copy directly
        c.locals[reg].free = false
        active.add reg
        copies.add (active[i], reg, reg)
      else:
        # needs an intermediate temporary, but don't allocate one until the
        # full output set was marked as active
        copies.add (active[i], reg, active[i])

  # XXX: the way temporaries are used is inefficient. Consider ``{a=b, b=a}``.
  #      Here, two temporaries and a total of 4 assignments would be used,
  #      even though 1 temporary and 3 assignments would suffice

  let targetNode = gr.conts[g.target].n

  if arity > g.edges.len:
    # handle the implicit argument
    let
      n   = gr.conts[g.target].nodes.a
      reg = c.nodeToReg[n]

    if c.locals[reg].free:
      # not part of the input set, no temporary or copy are needed
      c.locals[reg].free = false
      active[arity - 1] = reg
    else:
      # needs a temporary + copy
      let tmp = c.alloc(c.locals[reg].typ)
      active[arity - 1] = tmp
      c.temps[n] = tmp # remember that a temporary is needed
      # no copy is necessary for an exception handler; the Raise takes care
      # of that
      if tree[targetNode].kind != Except:
        copies.add (tmp, reg, reg)

  # allocate the temporaries:
  for (src, dst, tmp) in copies.mitems:
    if src == tmp:
      tmp = c.alloc(c.locals[tmp].typ)
      active.add tmp

  # mark used registers as free again:
  for it in active.items:
    c.locals[it].free = true

  # emit the actual code:
  changes.insert(tree, c.conts, at, tree[targetNode].kind):
    # if the target is an exception handler, the intermediate continuation has
    # to be one too
    if tree[targetNode].kind == Except:
      bu.add localRef(active[arity - 1])
    else:
      bu.subTree Params: discard

    bu.subTree Locals:
      for it in active.items:
        bu.add localRef(it)

    template copy(src, dst) =
      bu.subTree Asgn:
        bu.add localRef(dst)
        bu.subTree Copy:
          bu.add localRef(src)

    # emit the copies:
    for (src, dst, tmp) in copies.items:
      copy(src, tmp)
    for (src, dst, tmp) in copies.items:
      if dst != tmp:
        copy(tmp, dst)

    # emit the exit:
    if tree[targetNode].kind == Except:
      # re-raise the exception
      bu.subTree Raise:
        bu.subTree Copy:
          bu.add localRef(active[arity - 1])
        bu.subTree exit:
          bu.add Node(kind: Immediate, val: c.contMap[g.target])
    else:
      bu.subTree exit:
        bu.add Node(kind: Immediate, val: c.contMap[g.target])

proc lowerExpr(tree; n; active: seq[uint32], changes) =
  for it in tree.flat(n):
    if tree[it].kind == Local:
      changes.replace(it, localRef(active[tree[it].val]))

proc lowerExpr(tree; n; active: seq[uint32], bu: var Builder[NodeKind]) =
  # XXX: due to the lack of stacked changesets/trees, we have to copy
  #      everything
  var buf: seq[Node]
  for it in tree.flat(n):
    if tree[it].kind == Local:
      buf.add localRef(active[tree[it].val])
    else:
      buf.add tree[it]

  bu.add buf

proc lowerStmt(tree; n; active: seq[uint32], changes) =
  # patch all references to locals:
  for it in tree.flat(n):
    if tree[it].kind == Local:
      changes.replace(it, localRef(active[tree[it].val]))

func hasReturn(c: PassCtx, tree; n): bool =
  ## Whether the ``CheckedCall`` at `n` returns something.
  let typN =
    if tree[n, 0].kind == Proc:
      # fetch the type from the procedure definition
      tree.child(tree.child(tree.child(2), tree[n, 0].val.int), 0)
    else:
      tree.child(n, 0)

  tree[c.lookup(tree, tree[typN].typ), 0].kind != Void

func isExit(tree; n): bool =
  ## Whether the continuation at `n` is the procedure exit.
  tree.len(n) == 1

func getDest(c: PassCtx, gr; cont: Cont, g: int32): uint32 {.inline.} =
  ## Returns the register for the first parameter of the continuation targeted
  ## by edge group `g`.
  let node = gr.conts[gr.groups[g].target].nodes.a
  # use the temporary if available
  if node in c.temps: c.temps[node]
  else:               c.nodeToReg[node]

proc lowerCont(c; tree; gr; cont: Cont, self: int, changes) =
  let n = cont.n
  var active = newSeq[uint32](cont.nodes.len)
    ## list of registers active within the continuation

  # gather the list of active registers:
  for i in 0..<cont.nodes.len:
    active[i] = c.nodeToReg[cont.nodes.a + i]

  # patch references to locals:
  for stmt in tree.items(n, 2, ^2):
    lowerStmt(tree, stmt, active, changes)

  # update the jumps:
  var bias = 1'u32
  for g in gr.groups.toOpenArray(cont.groups.a, cont.groups.b).items:
    if g.needsCopy:
      c.insertCopies(tree, gr, g, self + 1, tree[g.n].kind, changes)

      if tree[g.n].kind == Loop:
        changes.changeKind(g.n, Continue) # turn into a normal continue

      changes.replace(tree.child(g.n, 0)):
        Node(kind: Immediate, val: c.contMap[self] + bias)
      # the next inserted continuation (if any) needs to have a higher ID:
      inc bias
    elif c.contMap.len > 0 and c.contMap[g.target] != g.target:
      # the target's ID changed, adjust
      changes.replace(tree.child(g.n, 0)):
        Node(kind: Immediate, val: c.contMap[g.target])

    # remove the argument list:
    changes.remove(tree, g.n, tree.len(g.n) - 1)

  # lower the exit:
  let exit = tree.last(n)
  case tree[exit].kind
  of CheckedCall:
    if c.hasReturn(tree, exit):
      let dst = c.getDest(gr, cont, cont.groups.a)
      active.addUnique(dst)
      # turn into an assignment:
      changes.changeKind(exit, CheckedCallAsgn)
      changes.insert(tree, exit, 0): localRef(dst)

    for it in tree.items(exit, 0, ^3):
      lowerExpr(tree, it, active, changes)
  of Continue:
    if tree.len(exit) == 3:
      let g = cont.groups.a
      if isExit(tree, gr.conts[gr.groups[g].target].n):
        lowerExpr(tree, tree.child(exit, 1), active, changes)
      else:
        let dst = c.getDest(gr, cont, g)
        active.addUnique(dst)
        # turn into an assignment:
        changes.insert(tree, n, tree.len(n) - 1, Asgn):
          bu.add localRef(dst)
          lowerExpr(tree, tree.child(exit, 1), active, bu)
        changes.remove(tree, exit, 1)

  of SelectBool, Raise:
    lowerExpr(tree, tree.child(exit, 0), active, changes)
  of Select:
    lowerExpr(tree, tree.child(exit, 1), active, changes)
  else:
    discard "nothing to do"

  # rewrite the parameter list:
  if tree[n].kind == Except:
    changes.replace(tree.child(n, 0)):
      localRef(active[0])
  else:
    changes.replace(tree.child(n, 0), Params):
      discard

  changes.replace(tree.child(n, 1), Locals):
    for it in active.items:
      bu.add localRef(it)

proc getType(tree; n; local: int): TypeId =
  ## Returns the type ID for `local`. `n` is the parent continuation's node.
  let numParams = tree.len(n, 0)
  if numParams > local:
    tree[tree.child(n, 0), local].typ
  else:
    tree[tree.child(n, 1), local - numParams].typ

proc lowerProc(c: var PassCtx, tree; n; changes) =
  c.conts = tree.child(n, 1)
  c.locals.setLen(0)
  # the other per-procedure state is reset as needed

  var gr = buildGraph(tree, c.conts)
  colorGraph(gr)

  # allocate the registers for all colors. We do this in a pre-pass because:
  # * some lowering (e.g., for ``Continue``-with-value) needs to "look ahead"
  # * copy detection needs to know the registers
  block:
    c.nodeToReg.setLen(gr.nodes.len)

    var colorToReg: Table[uint32, Register]
    for cont in gr.conts.items:
      # 1. fill already allocated ones
      for id in cont.nodes.items:
        var reg = colorToReg.getOrDefault(gr.nodes[id].color, high(Register))
        if reg != high(Register):
          c.locals[reg].free = false
          c.nodeToReg[id] = reg.uint32
        else:
          c.nodeToReg[id] = high(uint32) # mark as uninitialized

      # 2. allocate the rest and update the associated color
      for id in cont.nodes.items:
        if c.nodeToReg[id] == high(uint32):
          let reg = c.alloc(getType(tree, cont.n, id - cont.nodes.a))
          c.nodeToReg[id] = reg
          colorToReg[gr.nodes[id].color] = reg

      # 3. mark all registers as free again
      for id in cont.nodes.items:
        c.locals[c.nodeToReg[id]].free = true

  # compute where copies are needed and, if necessary, the continuation ID map
  block:
    var needCopies = false
    for g in gr.groups.mitems:
      for e in gr.edges.toOpenArray(g.edges.a, g.edges.b).items:
        if c.nodeToReg[e.src] != c.nodeToReg[e.dst]:
          g.needsCopy = true
          needCopies = true
          break

    if needCopies:
      # compute the old ID -> new ID map
      var bias = 0
      c.contMap.setLen(gr.conts.len)
      for i, cont in gr.conts.pairs:
        c.contMap[i] = uint32(i + bias)
        for g in gr.groups.toOpenArray(cont.groups.a, cont.groups.b).items:
          if g.needsCopy:
            inc bias
    else:
      c.contMap.setLen(0) # clear

  # apply the lowering to all continuations:
  for i, it in tree.pairs(c.conts):
    if tree.len(it) > 1: # ignore the return continuation
      c.lowerCont(tree, gr, gr.conts[i], i, changes)

  # set the list of locals:
  changes.insert(tree, n, 1, Locals):
    for it in c.locals.items:
      bu.add Node(kind: Type, val: it.typ.uint32)

proc lower*(tree): Changeset[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = PassCtx(types: tree.child(0))

  for it in tree.items(tree.child(2)):
    c.lowerProc(tree, it, result)
