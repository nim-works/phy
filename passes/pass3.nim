## Lowers |L3| code into |L1| code. This means:
## * turning path expressions into pointer (read, integer) arithmetic
## * turning copies from within aggregate locations into loads
## * turning assignments into aggregate locations into stores
## * turning aggregate assignments/stores/loads into memory copies
##
## Future Considerations
## ~~~~~~~~~~~~~~~~~~~~~
##
## Single field unions/records where the field:
## * has an offset of zero
## * is of primitive type
##
## could be unpacked. In addition, locals of record type that:
## * are never passed to procedures
## * never have their address taken
##
## could also be unpacked. However, both are optimizations that should happen
## at a higher level, since spawning locals at this level would require them
## to be physical, instead of logical, locals.

import
  std/[tables],
  passes/[builders, changesets, trees, spec],
  vm/[utils]

type
  Node = TreeNode[NodeKind]

  PassCtx = object
    addrType: Node
      ## the type of address values

    locals: NodeIndex
      ## index of the current procedure's list of locals

  BuilderOrChangeset = Builder[NodeKind] or ChangeSet[NodeKind]

const
  AggregateTypes = {Record, Array}

# shorten some common procedure signatures:
using
  c: PassCtx
  tree: PackedTree[NodeKind]
  changes: var ChangeSet[NodeKind]
  n: NodeIndex
  bu: var BuilderOrChangeset

template replace(bu: var Builder[NodeKind], n; k: NodeKind, body: untyped) =
  discard n
  bu.subTree k:
    body

template keep(bu: var Builder[NodeKind], tree; n) =
  bu.copyFrom(tree, n)

template keep(bu: var Builder[NodeKind], tree; n; body: untyped) =
  bu.subTree tree[n].kind:
    body

template skipTree(bu: var Builder[NodeKind], n; body: untyped) =
  discard n
  body # nothing to do, just eval body

template keep(changes; tree; n) =
  # a no-op; just evaluate `n`
  discard n

template keep(changes; tree; n; body: untyped) =
  # a no-op; just evaluate `n`
  discard n
  body

template skipTree(changes; n; body: untyped) =
  changes.replace(n):
    body

func imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

func resolve(tree; n: NodeIndex): NodeIndex =
  ## Returns the index of the type description for `typ`.
  if tree[n].kind == Type:
    tree.child(tree.child(0), tree[n].val)
  else:
    n

proc typeof(c; tree; n): NodeIndex =
  ## Computes the type ID for the ``path-elem``.
  case tree[n].kind
  of Local:
    tree.child(c.locals, tree[n].val.int)
  of Deref:
    tree.child(n, 0)
  of At:
    let arr = c.typeof(tree, tree.child(n, 0)) # type of the array
    tree.child(resolve(tree, arr), 2)
  of Field:
    let
      (a, b) = pair(tree, n)
      rec = c.typeof(tree, a) # type of the record type
    # +1 to skip the size node
    tree.child(tree.child(resolve(tree, rec), tree[b].val.int + 1), 1)
  else:
    unreachable()

proc sizeof(tree; n: NodeIndex): int =
  ## Returns the size of the type whose description is located at `n`.
  case tree[n].kind
  of Int, UInt, Float: tree[n].val.int
  of Record, Array:    tree[n, 0].val.int
  else:                unreachable()

proc lowerExpr(c; tree; n; bu: var BuilderOrChangeset)

proc lowerCall(c; tree; n; start: int, bu: var BuilderOrChangeset) =
  for it in tree.items(n, start + 1):
    c.lowerExpr(tree, it, bu)

proc lowerPathElem(c; tree; n; bu: var Builder[NodeKind]) =
  case tree[n].kind
  of Local:
    # locals appearing as a path element are turned into
    # ``(Addr <local>)``
    bu.subTree Addr:
      bu.add tree[n]
  of Deref:
    # only relevant for type information -> drop it
    c.lowerExpr(tree, tree.child(n, 1), bu)
  of Field, At:
    c.lowerExpr(tree, n, bu)
  else:
    unreachable()

proc lowerExpr(c; tree; n; bu: var BuilderOrChangeset) =
  ## Lowers the expression at `n`, if necessary. Trees are only modified when
  ## really needed, so ``lowerExpr`` is a generic procedure taking either a
  ## ``MirBuilder`` (within a modifed tree) or ``ChangeSet`` (within an
  ## unmodified tree) as the last parameter.
  case tree[n].kind
  of Local:
    bu.keep(tree, n)
  of At:
    let
      (a, b) = pair(tree, n)
      typ = resolve(tree, c.typeof(tree, n)) # element type
    # turn ``(At a b)`` into ``(Add a (Mul b elemSize))``
    bu.replace(n, Add):
      bu.add c.addrType
      c.lowerPathElem(tree, a, bu)
      # TODO: fold constant multiplications
      bu.subTree Mul:
        bu.add c.addrType
        # higher-level ILs ensure that the index type already has the correct
        # type
        c.lowerExpr(tree, b, bu)
        bu.add Node(kind: IntVal, val: uint32 sizeof(tree, typ))
  of Field:
    let
      (a, b) = pair(tree, n)
      typ = resolve(tree, c.typeof(tree, a))
    # turn into pointer arithmetic
    # TODO: omit the Add if the offset is 0
    bu.replace(n, Add):
      bu.add c.addrType
      c.lowerPathElem(tree, a, bu)
      let offset = tree[tree.child(typ, 1 + tree[b].imm), 0].imm
      bu.add Node(kind: IntVal, val: offset)
  of Copy:
    let
      a = tree.child(n, 0)
      typ = c.typeof(tree, a)
    if tree[a].kind in {Field, At}:
      # turn into a Load
      bu.replace(n, Load):
        bu.add tree[typ]
        c.lowerExpr(tree, a, bu)
    else:
      bu.keep(tree, n)
  of Addr:
    let a = tree.child(n, 0)
    if tree[a].kind in {Field, At}:
      # drop the ``Addr`` operation. The whole path expression will be turned
      # into pointer arithmetic
      bu.skipTree(n):
        c.lowerExpr(tree, a, bu)
    else:
      # can only be ``(Addr <local>)``, which doesn't need any lowering
      bu.keep(tree, n)

  elif isAtom(tree[n].kind):
    bu.keep(tree, n)
  else:
    # XXX: for simplicity, just traverse everything else, even the parts that
    #      aren't really expressions (such as the type references)
    bu.keep(tree, n):
      for it in tree.items(n):
        c.lowerExpr(tree, it, bu)

proc genMemCopy(c; tree; n, dst, src, typ: NodeIndex, changes) =
  ## Replaces the subtree at `n` with a ``Blit`` statement.
  changes.replace(n, Blit):
    # can be either an l- or rvalue, depending on who called ``genMemCopy``
    if tree[dst].kind in {Field, At, Local}:
      c.lowerPathElem(tree, dst, bu)
    else:
      c.lowerExpr(tree, dst, bu)

    case tree[src].kind
    of Copy:
      c.lowerPathElem(tree, tree.last(src), bu)
    of Load:
      # don't load a temporary value, copy from the source into the
      # destination directly
      c.lowerExpr(tree, tree.last(src), bu)
    else:
      # no other expression can evaluate to an aggregate value
      unreachable()

    # the size-in-bytes to copy. Take it from the type
    bu.add Node(kind: IntVal, val: uint32 sizeof(tree, resolve(tree, typ)))

proc lowerStmt(c; tree; n; changes) =
  case tree[n].kind
  of Asgn:
    let
      (a, b) = pair(tree, n)
      typN = c.typeof(tree, a)

    if tree[resolve(tree, typN)].kind in AggregateTypes:
      c.genMemCopy(tree, n, a, b, typN, changes)
    elif tree[a].kind in {Field, At}:
      # turn into a Store
      changes.replace(n, Store):
        bu.add tree[typN]
        c.lowerExpr(tree, a, bu)
        c.lowerExpr(tree, b, bu)
    else:
      c.lowerExpr(tree, a, changes)
      c.lowerExpr(tree, b, changes)
  of Store:
    let
      (t, a, b) = triplet(tree, n)
      typN = resolve(tree, t)

    if tree[typN].kind in AggregateTypes:
      c.genMemCopy(tree, n, a, b, typN, changes)
    else:
      c.lowerExpr(tree, a, changes)
      c.lowerExpr(tree, b, changes)
  of Blit:
    let (a, b, size) = triplet(tree, n)
    c.lowerExpr(tree, a, changes)
    c.lowerExpr(tree, b, changes)
    c.lowerExpr(tree, size, changes)
  of Clear:
    let (a, b) = pair(tree, n)
    c.lowerExpr(tree, a, changes)
    c.lowerExpr(tree, b, changes)
  of Drop:
    c.lowerExpr(tree, tree.child(n, 0), changes)
  of Call:
    c.lowerCall(tree, n, 0, changes)
  else:
    unreachable()

proc lowerExit(c; tree; n; changes) =
  case tree[n].kind
  of Continue:
    if tree.len(n) > 1:
      c.lowerExpr(tree, tree.child(n, 1), changes)
  of CheckedCallAsgn:
    c.lowerCall(tree, n, 1, changes)
  of CheckedCall:
    c.lowerCall(tree, n, 0, changes)
  of SelectBool, Raise:
    c.lowerExpr(tree, tree.child(n, 0), changes)
  else:
    discard "nothing to do"

proc lowerType(tree; n; changes) =
  case tree[n].kind
  of AggregateTypes:
    # turn into a blob type:
    changes.replace(n, Blob):
      bu.add tree[n, 0] # copy the size
  of ProcTy, Int, UInt, Float:
    discard "nothing to do"
  else:
    unreachable()

proc lowerProc(c: var PassCtx, tree; n; changes) =
  c.locals = tree.child(n, 1)
  assert tree[c.locals].kind == Locals
  # apply the lowering to all continuations:
  for it in tree.items(tree.child(n, 2)):
    if tree.len(it) > 1: # ignore the return continuation
      for stmt in tree.items(it, 2, ^2):
        c.lowerStmt(tree, stmt, changes)

      c.lowerExit(tree, tree.last(it), changes)

proc lower*(tree; ptrSize: int): Changeset[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of address values.

  # lower the types:
  for it in tree.items(tree.child(0)):
    lowerType(tree, it, result)

  var c = PassCtx(addrType: Node(kind: UInt, val: ptrSize.uint32))

  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      c.lowerProc(tree, it, result)
