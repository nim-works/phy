## Lowers |L4| into the |L3| language.

import
  std/[intsets, tables],
  passes/[builders, changesets, trees, spec],
  vm/[utils]

type
  TypeId = distinct uint32
  Node = TreeNode[NodeKind]

  PassCtx = object
    types: NodeIndex

    # procedure context:
    conts: NodeIndex
    locals: seq[tuple[typ: TypeId, free: bool]]
      ## all locals (effectively registers) allocated
    map: Table[int, seq[int]]
      ## continuation ID -> inputs

    bias: int ## the value to add all continuation ID onward

# shorten some common procedure signatures:
using
  c: var PassCtx
  tree: PackedTree[NodeKind]
  n: NodeIndex
  changes: var ChangeSet[NodeKind]

proc `==`(a, b: TypeId): bool {.borrow.}

func imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

func typ(n: Node): TypeId {.inline.} =
  assert n.kind == Type
  n.val.TypeId

func lookup(c: PassCtx; tree; typ: TypeId): NodeIndex =
  ## Returns the index of the type description for `typ`.
  tree.child(c.types, typ.int)

proc alloc(c; typ: TypeId): int =
  # XXX: maybe use a free-list instead
  for i, it in c.locals.mpairs:
    if it.free and it.typ == typ:
      it.free = false
      return i

  result = c.locals.len
  c.locals.add (typ, false)

proc push(c; tree; id: int, kind: NodeKind, args: sink seq[int], changes): bool =
  if id in c.map:
    # the target continuation already has a set of registers
    let target {.cursor.} = c.map[id]
    var map = newSeq[tuple[dst, src, tmp: int]]()

    for i, arg in args.pairs:
      if arg != target[i]:
        # a copy is required
        let (typ, free) = c.locals[target[i]]
        if free:
          # the register can be copied directly
          map.add (target[i], arg, target[i])
        else:
          # an intermediate temporary is needed
          let tmp = c.alloc(typ)
          map.add (target[i], arg, tmp)
          c.locals[tmp].free = true # free right away

    if map.len > 0:
      # at least one the source and destination use different registers ->
      # copies are required. This requires a new in-between continuation
      # FIXME: the new continuation is currently inserted at *the end*, which
      #        is necessary because inserting them before would mess up IDs
      #        and require patching all references, including those within
      #        newly inserted continuations. The problem is that this undoes
      #        the breadth-first order of continuations -- lower-level ILs
      #        tacitly allow this, but in the future, they shouldn't
      changes.insert(tree, c.conts, tree.len(c.conts), Continuation):
        bu.subTree Params: discard
        bu.subTree Locals:
          # the registers from the input set are alive:
          for it in args.items:
            bu.add Node(kind: Local, val: it.uint32)

          # ...and the destination registers from `map`. Note that temporaries
          # can be re-used multiple times
          var added: IntSet
          for (_, _, dst) in map.items:
            if not containsOrIncl(added, dst):
              bu.add Node(kind: Local, val: dst.uint32)

        # emit the copies:
        for (dst, src, tmp) in map.items:
          bu.subTree Asgn:
            bu.add Node(kind: Local, val: tmp.uint32)
            bu.subTree Copy:
              bu.add Node(kind: Local, val: src.uint32)

          if tmp != dst:
            # copy to the final destination
            bu.subTree Asgn:
              bu.add Node(kind: Local, val: dst.uint32)
              bu.subTree Copy:
                bu.add Node(kind: Local, val: tmp.uint32)

        # emit the exit:
        bu.subTree kind:
          bu.add Node(kind: Immediate, val: (id + c.bias + 1).uint32)

        result = true # an intermediate continuation was introduced
  else:
    c.map[id] = args

proc hasReturn(c: PassCtx, tree; n): bool =
  var typ: TypeId
  if tree[n, 0].kind == Proc:
    typ = tree[tree.child(tree.child(2), tree[n, 0].val.int), 0].typ
  else:
    typ = tree[n, 0].typ

  tree[c.lookup(tree, typ), 0].kind != Void

proc rewrite(c; tree; n; active: seq[int], inferFirst: bool; changes): int =
  let target = tree[n, 0].imm.int
  var args: seq[int]

  var inferFirst = inferFirst
  if inferFirst:
    if target in c.map:
      # the target already has a register associated with the parameter, use
      # that
      args.add c.map[target][0]
      inferFirst = false
      result = args[0]

  # process the drop-list first:
  assert tree[tree.last(n)].kind == List
  for it in tree.items(tree.last(n)):
    c.locals[active[tree[it].val]].free = true

  if inferFirst:
    # allocate *after* the drop-list, so that registers can be re-used
    args.add c.alloc(tree[tree.child(tree.child(c.conts, target), 0), 0].typ)
    result = args[0]

  case tree.len(n)
  of 3:
    # normal continue
    for it in tree.items(tree.child(n, 1)):
      args.add active[tree[it, 0].val]
  of 4:
    # eval + continue. Only valid for ``Continue``s targeting the return
    # continuation
    for it in tree.items(tree.child(n, 2)):
      args.add active[tree[it, 0].val]
  else:
    unreachable()

  if c.push(tree, target.int, tree[n].kind, args, changes):
    # patch the target
    if tree[n].kind == Loop:
      changes.changeKind(n, Continue)
    changes.replace(tree.child(n, 0)):
      Node(kind: Immediate, val: uint32(tree.len(c.conts) + c.bias))
    inc c.bias

  # restore the dropped locals, for further exits
  for it in tree.items(tree.last(n)):
    c.locals[active[tree[it].val]].free = false

  # remove the drop and move lists:
  changes.remove(tree, n, tree.len(n) - 1)
  changes.remove(tree, n, tree.len(n) - 2)

proc cont(c; tree; n; id: int, changes) =
  var locals: seq[int]
  discard c.map.pop(id, locals)

  # TODO: use a proper error reporting system here
  assert tree.len(tree.child(n, 0)) == locals.len, "arity mismatch"

  # allocate registers for the spawned locals:
  for it in tree.items(tree.child(n, 1)):
    locals.add c.alloc(tree[it].typ)

  proc exit(c; tree; n; locals: var seq[int], changes) =
    # TODO: use pattern matching for this instead; it'd be much more concise
    case tree[n].kind
    of Continue, Loop:
      discard rewrite(c, tree, n, locals, false, changes)
    of CheckedCall:
      if c.hasReturn(tree, n):
        changes.changeKind(n, CheckedCallAsgn)
        let
          target = tree.child(n, ^2)
          local = rewrite(c, tree, target, locals, true, changes)
        exit(c, tree, tree.child(n, ^1), locals, changes)

        # emit the assignment destination:
        changes.insert(tree, n, 0, Node(kind: Local, val: local.uint32))

        if tree.len(tree.child(c.conts, tree[target, 0].imm)) == 1:
          # the procedure exit is the target; an intermediate continuation is
          # needed
          changes.replace(tree.child(target, 0)):
            Node(kind: Immediate, val: uint32(tree.len(c.conts) + c.bias))
          inc c.bias
          changes.insert(tree, c.conts, tree.len(c.conts), Continuation):
            bu.subTree Params: discard
            bu.subTree Locals:
              bu.add Node(kind: Local, val: local.uint32)
            bu.subTree Continue:
              bu.add tree[target, 0]
              bu.subTree Copy:
                bu.add Node(kind: Local, val: local.uint32)

      else:
        exit(c, tree, tree.child(n, ^2), locals, changes)
        exit(c, tree, tree.child(n, ^1), locals, changes)
    of Raise:
      exit(c, tree, tree.child(n, 1), locals, changes)
    of SelectBool:
      exit(c, tree, tree.child(n, 1), locals, changes)
      exit(c, tree, tree.child(n, 2), locals, changes)
    of Select:
      for it in tree.items(n, 2):
        exit(c, tree, tree.last(it), locals, changes)
    of Unwind:
      discard "nothing to do"
    else:
      unreachable()

  exit(c, tree, tree.last(n), locals, changes)

  # set the list of active locals:
  changes.replace(tree.child(n, 1), Locals):
    for it in locals.items:
      bu.add Node(kind: Local, val: it.uint32)
      c.locals[it].free = true

proc lowerStmt(c; tree; n; changes) =
  for it in tree.flat(n):
    if tree[it].kind == Local:
      changes.replace(it, Node(kind: Local, val: 0))

proc lowerProc(c: var PassCtx, tree; n; changes) =
  c.conts = tree.child(n, 1)
  c.map.clear()
  c.locals.setLen(0)
  c.bias = 0

  block:
    # handle the parameters:
    let typ = c.lookup(tree, tree[n, 0].typ)
    var params: seq[int]
    for it in tree.items(typ, 1):
      params.add c.alloc(tree[it].typ)

    # pass to the entry continuation:
    c.map[0] = params

  # apply the lowering to all continuations:
  for i, it in tree.pairs(c.conts):
    if tree.len(it) > 1: # ignore the return continuation
      for stmt in tree.items(it, 2, ^2):
        c.lowerStmt(tree, stmt, changes)

      # remove the parameters from the list:
      changes.replace(tree.child(it, 0), Params):
        discard

      c.cont(tree, it, i, changes)

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
