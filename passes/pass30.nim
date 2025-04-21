## Lowers |L30| into the |L25| language. The pass flattens the input statements
## by replacing the |L30| control-flow constructs with the goto-esque |L25|
## control-flow statements.

import
  std/options,
  passes/[builders, changesets, trees, syntax]

type
  Node = TreeNode[NodeKind]
  LabelId = uint32

  PassCtx = object
    types: NodeIndex

    # per-procedure state:
    locals: NodeIndex

    nextLabel: uint32
      ## the ID to use for the next label. Incremented when "allocating" a
      ## label
    context: seq[Option[LabelId]]
      ## stack of block context objects. For each block-like structure, a new
      ## entry is pushed

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

proc newLabel(c): LabelId =
  result = c.nextLabel.LabelId
  inc c.nextLabel

proc reserve(c; label: var Option[LabelId]): LabelId =
  ## Unwraps `label`, allocating a new label and updating `label` with it if
  ## `label` is not yet initialized.
  if label.isSome:
    result = label.unsafeGet
  else:
    result = c.newLabel()
    label = some(result)

proc join(bu; label: LabelId) =
  bu.subTree Join:
    bu.add Node(kind: Immediate, val: label)

proc goto(bu; label: LabelId) =
  bu.subTree Goto:
    bu.add Node(kind: Immediate, val: label)

proc pushContext(c) =
  c.context.add none(LabelId)

proc popContext(c; bu): bool =
  ## Pops the context for some structured control-flow construct. Returns
  ## 'true' when structured control-flow never leaves the construct, false
  ## otherwise.
  let label = c.context.pop()
  result = label.isNone # no label means "exit is never reached"
  if not result:
    bu.join(label.unsafeGet)

proc leave(c; blk: int): LabelId =
  ## Registers a jump to the exit of the given block-like control-flow
  ## construct.
  c.reserve(c.context[^blk])

proc lowerStmt(c; tree; n, bu): bool

proc lowerBody(c; tree; n, bu) =
  if not c.lowerStmt(tree, n, bu):
    bu.goto(c.leave(1))

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
    bu.goto(c.leave(tree[n, 0].imm.int + 1))
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
    let label = c.newLabel()
    bu.join(label)

    c.pushContext()
    if not c.lowerStmt(tree, tree.child(n, 0), bu):
      # add a back edge:
      bu.subTree Loop:
        bu.add Node(kind: Immediate, val: label)

    result = c.popContext(bu)
  of If:
    c.pushContext()
    case tree.len(n)
    of 2: # if-then
      let
        (cond, a) = tree.pair(n)
        then      = c.newLabel()

      bu.subTree Branch:
        bu.copyFrom(tree, cond)
        bu.goto(c.leave(1)) # the false branch
        bu.goto(then)       # the true branch

      bu.join(then)
      c.lowerBody(tree, a, bu)
    of 3: # if-then-else
      let
        (cond, a, b) = tree.triplet(n)
        then         = c.newLabel()
        els          = c.newLabel()

      bu.subTree Branch:
        bu.copyFrom(tree, cond)
        bu.goto(els)  # the false branch
        bu.goto(then) # the true branch

      bu.join(then)
      c.lowerBody(tree, a, bu)
      bu.join(els)
      c.lowerBody(tree, b, bu)
    else:
      unreachable()

    result = c.popContext(bu)
  of Case:
    var branches = newSeq[(NodeIndex, LabelId)]()
    # emit the Select statement and gather the case branches:
    bu.subTree Select:
      bu.copyFrom(tree, tree.child(n, 0))
      bu.copyFrom(tree, tree.child(n, 1))
      for it in tree.items(n, 2):
        bu.subTree Choice:
          bu.copyFrom(tree, tree.child(it, 0))
          let label = c.newLabel()
          branches.add (tree.child(it, 1), label)
          bu.goto(label)

    # emit the case branch bodies:
    c.pushContext()
    for (pos, label) in branches.mitems:
      bu.join(label)
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
  c.nextLabel = 0
  c.locals = tree.child(n, 2)

  changes.replace(tree.child(n, 3), Stmts):
    # the body of a procedure must always end with a terminator
    doAssert c.lowerStmt(tree, tree.child(n, 3), bu),
              "control-flow falls out of the body"

  assert c.context.len == 0, "context stack is not empty"

proc lower*(tree): Changeset[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = PassCtx(types: tree.child(0))

  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      c.lowerProc(tree, it, result)
