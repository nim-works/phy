## Lowers |L10| into the |L7| language. The pass flattens the input statements
## by replacing the |L10| control-flow constructs with the goto-esque |L7|
## control-flow statements.

import
  passes/[builders, changesets, trees, spec],
  vm/utils

type
  Node = TreeNode[NodeKind]

  PassCtx = object
    types: NodeIndex

    # per-procedure state:
    locals: NodeIndex

    nextLabel: uint32
      ## the ID to use for the next label. Incremented when "allocating" a
      ## label
    blockExits: seq[seq[Placeholder]]

# shorten some common procedure signatures:
using
  c: var PassCtx
  tree: PackedTree[NodeKind]
  n: NodeIndex
  changes: var ChangeSet[NodeKind]
  bu: var Builder[NodeKind]

func imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

proc pushContext(c) =
  c.blockExits.add default(seq[Placeholder])

proc join(c; bu): uint32 =
  result = c.nextLabel
  inc c.nextLabel

  bu.subTree Join:
    bu.add Node(kind: Immediate, val: result)

proc complete(c; p: sink Placeholder, label: uint32, bu) =
  bu.replace(p, Node(kind: Immediate, val: label))

proc popContext(c; bu): bool =
  ## Pops the context for some structured control-flow construct. Returns
  ## 'true' when structured control-flow never leaves the construct, false
  ## otherwise.
  var exits = c.blockExits.pop()
  result = exits.len == 0
  if not result:
    let label = c.join(bu)
    for e in exits.mitems:
      c.complete(move e, label, bu)

proc leave(c; p: sink Placeholder, blk: int) =
  ## Registers a jump to the end of the given context. `p` is later replaced
  ## with the label of the join point.
  c.blockExits[^blk].add p

proc lowerStmt(c; tree; n, bu): bool

proc lowerBody(c; tree; n, bu) =
  if not c.lowerStmt(tree, n, bu):
    bu.subTree Continue:
      c.leave(bu.placeholder(), 1)

{.push warning[ProveInit]: off.}
proc hack*(): Placeholder =
  ## Used to initialize a ``Placeholder`` variable where the compiler isn't
  ## able to figure that a local is in fact assigned to before it's used.
  discard
{.pop.}

proc lowerStmt(c; tree; n, bu): bool =
  ## Lowers an |L10| nested statement into a flat sequence of statements,
  ## which are directly emitted to `bu`. Returns 'false' when the statement
  ## has a structured exit, that is, when control-flow "falls out" of it --
  ## 'true' otherwise.
  case tree[n].kind
  of Unreachable:
    bu.subTree Unreachable:
      discard
    result = true
  of Break:
    bu.subTree Continue:
      c.leave(bu.placeholder(), tree[n, 0].imm.int + 1)
    result = true
  of Return:
    bu.copyFrom(tree, n)
    result = true
  of Raise:
    bu.subTree Raise:
      bu.copyFrom(tree, tree.child(n, 0))
      bu.subTree Unwind:
        discard
    result = true
  of CheckedCall, CheckedCallAsgn:
    bu.subTree tree[n].kind:
      for it in tree.items(n):
        bu.copyFrom(tree, it)
      bu.subTree Unwind: discard
  of Block:
    c.pushContext()
    c.lowerBody(tree, tree.child(n, 0), bu)
    result = c.popContext(bu)
  of Loop:
    let label = c.join(bu)

    c.pushContext()
    if not c.lowerStmt(tree, tree.child(n, 0), bu):
      # add a back edge:
      bu.subTree Loop:
        bu.add Node(kind: Immediate, val: label)

    result = c.popContext(bu)
  of If:
    # XXX: language shortcoming workaround. Both then and els are
    #      initialized before their first use, but not explicitly
    #      initializing them as part of the declaration is an error...
    var then, els = hack()

    bu.subTree SelectBool:
      bu.copyFrom(tree, tree.child(n, 0))
      bu.subTree Continue: # the false branch
        els = bu.placeholder()
      bu.subTree Continue: # the true branch
        then = bu.placeholder()

    c.pushContext()
    case tree.len(n)
    of 2: # if-then
      let (_, a) = tree.pair(n)
      c.complete(then, c.join(bu), bu)
      c.lowerBody(tree, a, bu)
      c.leave(els, 1)
    of 3: # if-then-else
      let (_, a, b) = tree.triplet(n)
      c.complete(then, c.join(bu), bu)
      c.lowerBody(tree, a, bu)
      c.complete(els, c.join(bu), bu)
      c.lowerBody(tree, b, bu)
    else:
      unreachable()

    result = c.popContext(bu)
  of Case:
    var branches = newSeq[(NodeIndex, Placeholder)]()
    # emit the Select statement and gather the case branches:
    bu.subTree Select:
      bu.copyFrom(tree, tree.child(n, 0))
      bu.copyFrom(tree, tree.child(n, 1))
      for it in tree.items(n, 2):
        bu.subTree Choice:
          bu.copyFrom(tree, tree.child(it, 0))
          bu.subTree Continue:
            branches.add (tree.child(it, 1), bu.placeholder())

    # emit the case branch bodies:
    c.pushContext()
    for (pos, ph) in branches.mitems:
      c.complete(move ph, c.join(bu), bu)
      c.lowerBody(tree, pos, bu)

    result = c.popContext(bu)
  of Stmts:
    for i, it in tree.pairs(n):
      if c.lowerStmt(tree, it, bu):
        assert i == tree.len(n) - 1, "unculled unreachable code detected"
        result = true
        break
  else:
    bu.copyFrom(tree, n)

proc lowerProc(c: var PassCtx, tree; n; changes) =
  c.blockExits.shrink(0)
  c.nextLabel = 0
  c.locals = tree.child(n, 1)

  changes.replace(tree.child(n, 2), Stmts):
    # the body of a procedure must always end with a terminator
    doAssert c.lowerStmt(tree, tree.child(n, 2), bu),
              "control-flow falls out of the body"

proc lower*(tree): Changeset[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = PassCtx(types: tree.child(0))

  for it in tree.items(tree.child(2)):
    c.lowerProc(tree, it, result)
