## Lowers |L3| code into |L1| code. This means:
## * turning path expressions into pointer (read, integer) arithmetic
## * collapsing address-of operations
## * collapsing aggregate stores/loads
## * removing all aggregate types

import
  std/[options, tables],
  passes/[changesets, trees, spec],
  vm/[utils]

type
  TypeId = distinct uint32
  Node = TreeNode[NodeKind]

  PassCtx = object
    types: NodeIndex
    addrType: TypeId
      ## the type of address values

    typeMap: Table[TypeId, TypeId]
      ## maps old type IDs to new ones. If there's no entry in table for a
      ## type, it means that the type was removed

# shorten some common procedure signatures:
using
  c: PassCtx
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var Cursor[NodeKind]

proc `==`(x, y: TypeId): bool {.borrow.}

func imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

func typ(n: Node): TypeId {.inline.} =
  assert n.kind == Type
  n.val.TypeId

func lookup(c; tree; typ: TypeId): NodeIndex =
  ## Returns the index of the type description for `typ`.
  tree.child(c.types, typ.int)

func sizeof(c; tree; typ: TypeId): uint64 =
  ## Returns the numbers of byte `typ` occupies in memory.
  let n = c.lookup(tree, typ)
  case tree[n].kind
  of Record, Union, Array:
    tree[n, 0].imm.uint64
  of UInt, Int, Float:
    tree[n, 0].imm.uint64
  else:
    unreachable()

func lookupField(c; tree; typ: TypeId, field: int): (uint64, TypeId) =
  let n = c.lookup(tree, typ)
  let field = tree.child(n, 2 + field)
  case tree[n].kind
  of Record:
    result = (tree[field, 0].imm.uint64, tree[field, 1].typ)
  of Union:
    result = (0'u64, tree[field].typ)
  else:
    unreachable()

proc lowerExpr(c; tree; bu)
proc lowerPath(c; tree; bu): TypeId

proc computeOffset(c; tree; n): (uint64, TypeId) =
  ## Computes the static relative offset and type for path expression `n`.
  case tree[n].kind
  of Deref:
    result = (0'u64, tree[n, 0].typ)
  of Field:
    let
      (a, b) = tree.pair(n)
      (offset, typ) = c.computeOffset(tree, a)
    result = c.lookupField(tree, typ, tree[b].imm.int)
    result[0] += offset
  of At:
    let
      (a, b) = tree.pair(n)
      (offset, typ) = c.computeOffset(tree, a)
      elem = tree[c.lookup(tree, typ), 2].typ
    if tree[b].kind == IntVal:
      # static indexing
      result = (offset + (tree.getUInt(b) * c.sizeof(tree, elem)), elem)
    else:
      # dynamic indexing
      result = (0'u64, elem)
  else:
    unreachable()

proc lowerPathElem(c; tree; bu) =
  ## Lowers the path expression at the current cursor position.
  let n = bu.pos
  case tree[n].kind
  of Deref:
    assert tree[n, 1].kind in {Move, Copy, IntVal}
    # replace the Deref with its content:
    bu.skipTree tree:
      bu.skip(tree)
      bu.keep(tree)
  of Field:
    bu.skipTree tree:
      c.lowerPathElem(tree, bu)
      bu.skip(tree)
  of At:
    # XXX: the branching logic here might be an indicator for a ``DynAt``
    #      being a good idea...
    if tree[n, 1].kind == IntVal:
      # static indexing
      bu.skipTree tree:
        c.lowerPathElem(tree, bu)
        bu.skip(tree)
    else:
      # dynamic indexing
      bu.skipTree tree:
        bu.subTree Add:
          bu.add Node(kind: Type, val: c.addrType.uint32)
          let typ = c.lowerPath(tree, bu)
          bu.subTree Mul:
            bu.add Node(kind: Type, val: c.addrType.uint32)
            c.lowerExpr(tree, bu)
            bu.add Node(kind: IntVal, val: uint32 c.sizeof(tree, tree[c.lookup(tree, typ), 2].typ))

  else:
    unreachable()

proc lowerPath(c; tree; bu): TypeId =
  let (offset, typ) = c.computeOffset(tree, bu.pos)
  if offset == 0:
    # no offset is needed
    c.lowerPathElem(tree, bu)
  else:
    # add the static offset to the address value
    bu.subTree Add:
      bu.add Node(kind: Type, val: c.addrType.uint32)
      c.lowerPathElem(tree, bu)
      # TODO: this needs to use packed integers
      bu.add Node(kind: IntVal, val: offset.uint32)

  result = typ

proc updateType(c; tree; bu) =
  let typ  = tree[bu.pos].typ
  assert typ in c.typeMap
  let with = c.typeMap[typ]
  # don't modify nodes if they don't change; it keeps the changeset
  # smaller
  if typ == with:
    bu.keep(tree)
  else:
    bu.replace tree, Node(kind: Type, val: with.uint32)

proc lowerExpr(c; tree; bu) =
  ## Lowers expressions. If the sub-tree at `bu` is not an expression, it's
  ## kept, but expressions within are lowered.
  case tree[bu.pos].kind
  of Load:
    bu.keepTree tree:
      c.lowerExpr(tree, bu)
      c.lowerExpr(tree, bu)
  of At, Field:
    # handled here for the convenience of the callers
    discard c.lowerPath(tree, bu)
  of Addr:
    bu.skipTree tree:
      discard c.lowerPath(tree, bu)
  of Type:
    c.updateType(tree, bu)
  else:
    bu.filterTree tree, {Addr, Type, Load}:
      c.lowerExpr(tree, bu)

proc lowerStmt(c; tree; bu) =
  case tree[bu.pos].kind
  of Store:
    let t = tree[bu.pos, 0].typ
    if t in c.typeMap:
      bu.keepTree tree:
        c.lowerExpr(tree, bu)
        c.lowerExpr(tree, bu)
        c.lowerExpr(tree, bu)
    else:
      # it's a store with an aggregate type.
      # ``(Store ... x (Load ... y))`` -> ``(Copy x y size)``
      bu.skipTree tree:
        bu.skip(tree)
        bu.subTree Copy:
          c.lowerExpr(tree, bu)
          assert tree[bu.pos].kind == Load,
                 "aggregate Store source can only be a Load"
          # drop the Load
          bu.skipTree tree:
            bu.skip(tree)
            c.lowerExpr(tree, bu)
          bu.add Node(kind: IntVal, val: uint32 c.sizeof(tree, t))
  of Asgn, Copy, Clear, Drop, Call:
    # no special handling, only lower the expressions within
    c.lowerExpr(tree, bu)
  else:
    unreachable()

proc lowerProc(c: var PassCtx, tree; bu) =
  bu.keepTree tree:
    c.lowerExpr(tree, bu) # update the type reference
    bu.keep(tree)

    bu.forEach tree, n:
      bu.keepTree tree:
        # update the type references for the parameters and locals list
        bu.forEach tree, n:
          c.updateType(tree, bu)
        bu.forEach tree, n:
          c.updateType(tree, bu)

        for _ in 2..<tree.len(n)-1:
          c.lowerStmt(tree, bu)

        c.lowerExpr(tree, bu) # no special handling for exits

proc lower*(tree; ptrSize: int): Changeset[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of address values.
  var c = PassCtx(types: tree.child(0))
  var bu = initCursor[NodeKind](tree)

  var addrType = none(TypeId)
  bu.keepTree tree:
    var id = 0
    # remove all aggregate types from the type section:
    for i, it in tree.pairs(tree.child(0)):
      case tree[it].kind
      of Record, Union, Array:
        bu.skip(tree)
      of Int, UInt, Float:
        # if a uint type fits, pick it as the address type:
        if tree[it].kind == UInt and addrType.isNone and
           tree[it, 0].imm.int == ptrSize:
          addrType = some TypeId(id)

        bu.keep(tree)
        c.typeMap[TypeId(i)] = TypeId(id)
        inc id
      of ProcTy:
        # patch the types referenced by proc types
        bu.forEach tree, n:
          if tree[n].kind == Type:
            c.updateType(tree, bu)
          else:
            bu.keep(tree) # must be ``Void``

        c.typeMap[TypeId(i)] = TypeId(id)
        inc id
      else:
        unreachable()

    if addrType.isSome:
      # reuse an existing type
      c.addrType = addrType.unsafeGet
    else:
      # no type that can be re-used; add a new one
      bu.subTree UInt:
        bu.add Node(kind: Immediate, val: ptrSize.uint32)
      c.addrType = TypeId(id)

  bu.keep(tree) # keep the globals

  bu.forEach tree, n:
    c.lowerProc(tree, bu)

  result = toChangeset(bu)
