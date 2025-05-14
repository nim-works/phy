## Turns all aggregate types into blob types. Path expression are turned into
## address value arithmetic (|L3| -> |L3|).

import
  passes/[changesets, syntax, trees]

type
  Context = object
    ptrSize: int
    # per-procedure state:
    locals: NodeIndex

using
  c: Context
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var ChangeSet[NodeKind]

proc typeof(c; tree; n): NodeIndex =
  case tree[n].kind
  of Local: tree.child(c.locals, tree[n].val)
  of Deref: tree.child(n, 0)
  else:     unreachable()

proc resolve(tree; n): NodeIndex =
  if tree[n].kind == Type:
    tree.child(tree.child(0), tree[n].val)
  else:
    n

proc size(tree; n: NodeIndex): uint =
  ## `n` must be the node index of a type description.
  case tree[n].kind
  of Record, Union, Array: tree[n, 0].val.uint
  of Int, UInt, Float:     tree[n].val.uint
  else:                    unreachable()

proc alignment(tree; n: NodeIndex): uint =
  ## `n` must be the node index of a type description.
  case tree[n].kind
  of Record, Union, Array: tree[n, 1].val.uint
  else:                    unreachable()

proc elementOffset(tree; n: NodeIndex, elem: uint32): uint =
  ## `n` must be the node index of a type description.
  case tree[n].kind
  of Union:  0'u
  of Record: tree[tree.child(n, elem + 2), 0].val
  of Array:  size(tree, tree.resolve(tree.child(n, 3))) * elem
  else:      unreachable()

proc typeOfElem(tree; n: NodeIndex, elem: uint32): NodeIndex =
  ## `n` must be the node index of a type description.
  case tree[n].kind
  of Record: tree.child(tree.child(n, elem + 2), 1)
  of Union:  tree.child(n, 2 + elem)
  of Array:  tree.child(n, 3)
  else:      unreachable()

proc loweredExpr(c; tree; n; bu): VirtualTree

proc lowerPath(c; tree; n; bu): VirtualTree =
  ## (Path typ root ...) -> (Add pointer_type (Addr root) ...)
  ## (Path typ (Deref t root) ...) -> (Add pointer_type root ...)
  result =
    case tree[n, 1].kind
    of Local: bu.buildTree tree(Addr, node(tree[n, 1]))
    of Deref: c.loweredExpr(tree, tree.child(tree.child(n, 1), 1), bu)
    else:     unreachable()

  var
    offset = 0'u
    typ = tree.resolve(c.typeof(tree, tree.child(n, 1)))

  for it in tree.items(n, 2):
    if tree[it].kind == Immediate:
      # a static field or array access
      offset += elementOffset(tree, typ, tree[it].val)
      typ = tree.resolve(typeOfElem(tree, typ, tree[it].val))
    elif tree[it].kind == IntVal:
      # a static array access
      offset += elementOffset(tree, typ, tree.getInt(it).uint32)
      typ = tree.resolve(typeOfElem(tree, typ, 0))
    else:
      # an array access with a dynamic index
      if offset > 0:
        # TODO: create a proper IntVal node once the ChangeSet API supports
        #       adding new packed numbers
        # add the static offset computed so far:
        result = bu.buildTree:
          tree(Offset,
            embed(result),
            node(IntVal, offset.uint32),
            node(IntVal, 1))
        offset = 0

      typ = tree.resolve(typeOfElem(tree, typ, 0))

      # apply the dynamic array element offset:
      result = bu.buildTree:
        tree(Offset,
          embed(result),
          embed(c.loweredExpr(tree, it, bu)),
          node(IntVal, size(tree, typ).uint32))

  if offset > 0:
    result = bu.buildTree:
      tree(Offset,
        embed(result),
        node(IntVal, offset.uint32),
        node(IntVal, 1))

proc lowerExpr(c; tree; n; bu) =
  case tree[n].kind
  of Copy:
    let x = tree.child(n, 0)
    if tree[x].kind == Path:
      # (Copy (Path typ ...)) -> (Load typ ...)
      bu.replace n,
        bu.newTree(Load,
          toVirtual tree.child(x, 0),
          c.lowerPath(tree, x, bu))
  of Addr:
    let x = tree.child(n, 0)
    if tree[x].kind == Path:
      # the path expression is turned into an address value; Addr is no longer
      # needed
      bu.replace n, lowerPath(c, tree, x, bu)
  of Path:
    bu.replace n, lowerPath(c, tree, n, bu)
  else:
    for it in tree.filter(n, {Copy, Addr}):
      c.lowerExpr(tree, it, bu)

proc loweredExpr(c; tree; n; bu): VirtualTree =
  bu.openTree(tree, n, c.lowerExpr(tree, n, bu))

proc lowerStmt(c; tree; n; bu) =
  case tree[n].kind
  of Asgn:
    let (a, b) = tree.pair(n)
    if tree[a].kind == Path:
      # (Asgn (Path typ ...) y) -> (Store typ ... y')
      bu.replace n,
        bu.newTree(Store,
          toVirtual tree.child(a, 0),
          c.lowerPath(tree, a, bu),
          c.loweredExpr(tree, b, bu))
    else:
      c.lowerExpr(tree, a, bu)
      c.lowerExpr(tree, b, bu)
  else:
    # no statement-specific transformation, just lower the expressions within
    c.lowerExpr(tree, n, bu)

proc lower*(tree; ptrSize: Positive): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of a pointer value.

  # turn all aggregate types into blob types:
  for it in tree.items(tree.child(0)):
    if tree[it].kind in {Record, Union, Array}:
      result.replace it:
        result.buildTree:
          tree(Blob,
            node(Immediate, uint32 size(tree, it)),
            node(Immediate, uint32 alignment(tree, it)))

  # lower the procedures:
  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      let
        (_, locals, body) = tree.triplet(it)
        c = Context(ptrSize: ptrSize, locals: locals)

      for blk in tree.items(body):
        for s in tree.items(blk, 1):
          c.lowerStmt(tree, s, result)
