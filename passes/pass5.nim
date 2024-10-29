## Lowers |L5| into the |L3| code. The pass is responsible for computing the
## stack layout and turning all ``Loc`` access into loads/stores relative to
## the frame pointer.

import
  passes/[changesets, trees, spec],
  vm/utils

type
  TypeId = distinct uint32
  Node = TreeNode[NodeKind]

  PassCtx = object
    types: NodeIndex
    addrType: TypeId
      ## the type to use for pointers and address arithmetic

    # per-procedure state:
    slots: NodeIndex
    offsets: seq[uint64]
      ## for each stack slot, the relative offset to the frame pointer where
      ## the slot is located in memory

    # per-block state:
    framePointer: uint32
      ## the ID of the parameter holding the frame pointer

const InterestingExpr = {Addr, Loc, Copy, Move}

# shorten some common procedure signatures:
using
  c: PassCtx
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var Cursor[NodeKind]

func align(size, align: uint64): uint64 =
  let mask = align - 1
  result = (size + mask) and not mask

func imm(n: Node): uint32 {.inline.} =
  assert n.kind == Immediate
  n.val

func typ(n: Node): TypeId {.inline.} =
  assert n.kind == Type
  n.val.TypeId

func getType(c; tree; slot: uint32): TypeId =
  ## Returns the type ID for `local`. `n` is the parent continuation's node.
  tree[c.slots, slot].typ

func lookup(c; tree; typ: TypeId): NodeIndex =
  ## Returns the index of the type description for `typ`.
  tree.child(c.types, typ.int)

func lookupField(c; tree; typ: TypeId, field: int): TypeId =
  let
    n = c.lookup(tree, typ)
    field = tree.child(n, 2 + field)

  case tree[n].kind
  of Record: tree[field, 1].typ
  of Union:  tree[field].typ
  else:      unreachable()

func typeof(c; tree; n): TypeId =
  ## Computes and returns the type of a path expression.
  case tree[n].kind
  of Loc:
    result = c.getType(tree, tree[n].val)
  of Field:
    let (a, b) = tree.pair(n)
    result = c.typeof(tree, a)
    result = c.lookupField(tree, result, tree[b].imm.int)
  of At:
    result = c.typeof(tree, tree.child(n, 0))
    result = tree[c.lookup(tree, result), 2].typ
  else:
    unreachable()

func sizeAndAlign(c; tree; typ: TypeId): (uint32, uint32) =
  let n = c.lookup(tree, typ)
  case tree[n].kind
  of Record, Union:
    let (size, align) = tree.pair(n)
    result = (tree[size].imm, tree[align].imm)
  of Array:
    let (size, _, typ) = tree.triplet(n)
    # the alignment must be computed from the element type
    result = (tree[size].imm, c.sizeAndAlign(tree, tree[typ].typ)[1])
  of UInt, Int, Float:
    let width = tree[n, 0].imm
    # size and alignment are both equal to the byte-width
    result = (width, width)
  else:
    unreachable()

template toNode(typ: TypeId): Node =
  Node(kind: Type, val: typ.uint32)

proc genLoc(c; id: uint32, bu) =
  if c.offsets[id] > 0:
    bu.subTree Add:
      bu.add toNode(c.addrType)
      bu.subTree Copy:
        bu.add Node(kind: Param, val: c.framePointer)
      bu.add Node(kind: IntVal, val: c.offsets[id].uint32)
  else:
    bu.subTree Copy:
      bu.add Node(kind: Param, val: c.framePointer)

proc lowerExpr(c; tree; bu) =
  let n = bu.pos
  case tree[n].kind
  of Loc:
    # must be the root of a path expression
    bu.skip(tree)
    bu.subTree Deref:
      bu.add toNode(c.getType(tree, tree[n].val))
      c.genLoc(tree[n].val, bu)
  of Move, Copy:
    let src = tree.child(n, 0)
    case tree[src].kind
    of At, Field:
      bu.skipTree tree:
        bu.subTree Load:
          bu.add toNode(c.typeof(tree, src))
          bu.subTree Addr:
            c.lowerExpr(tree, bu)
    of Loc:
      bu.skipTree tree:
        bu.subTree Load:
          bu.add toNode(c.getType(tree, tree[src].val))
          bu.skip(tree)
          c.genLoc(tree[src].val, bu)
    else:
      bu.keep(tree)
  of Addr:
    if tree[n, 0].kind == Loc:
      # replace the address-of operation with the address
      bu.skipTree tree:
        bu.skip(tree)
        c.genLoc(tree[n, 0].val, bu)
    else:
      bu.keepTree tree:
        c.lowerExpr(tree, bu)
  else:
    bu.filterTree tree, {Loc, Move, Copy, Addr}:
      c.lowerExpr(tree, bu)

proc lowerStmt(c; tree; bu) =
  # patch all references to locals:
  let n = bu.pos
  case tree[n].kind
  of StorageLive, StorageEnd:
    # not needed anymore
    bu.skip(tree)
  of Asgn:
    let dst = tree.child(n, 0)
    case tree[dst].kind
    of At, Field:
      bu.skipTree tree:
        bu.subTree Store:
          bu.add toNode(c.typeof(tree, dst))
          bu.subTree Addr:
            c.lowerExpr(tree, bu)
          c.lowerExpr(tree, bu)
    of Loc:
      bu.skipTree tree:
        bu.subTree Store:
          bu.skip(tree)
          bu.add toNode(c.getType(tree, tree[dst].val))
          c.genLoc(tree[dst].val, bu)
          c.lowerExpr(tree, bu)
    else:
      c.lowerExpr(tree, bu)
  else:
    c.lowerExpr(tree, bu)

proc lowerExit(c; tree; bu) =
  case tree[bu.pos].kind
  of Goto, Loop:
    # append the frame pointer parameter as an argument
    bu.keepTree tree:
      bu.keep(tree)
      bu.append tree:
        bu.add Node(kind: Param, val: c.framePointer)
  else:
    # process the interesting parts:
    bu.filterTree tree, {Goto} + InterestingExpr:
      if tree[bu.pos].kind == Goto:
        c.lowerExit(tree, bu)
      else:
        c.lowerExpr(tree, bu)

proc lowerProc(c: var PassCtx; tree; bu) =
  let n = bu.pos
  c.slots = tree.child(n, 1)
  c.offsets.setLen(tree.len(c.slots))

  # XXX: stack space is currently allocated in the most simplistic way, namely
  #      by laying out all locs sequentially without taking live ranges into
  #      account
  var pt = 0'u64
  for i, it in tree.pairs(c.slots):
    let (size, alignment) = c.sizeAndAlign(tree, tree[it].typ)
    doAssert alignment <= 8,
             "over-aligned stack locations are currently not supported"
    # XXX: over-aligned stack locations need support by the L0. In addition to
    #      the stack *size*, procedures also need to specify their expected
    #      stack *alignment*
    pt = align(pt, alignment)
    c.offsets[i] = pt
    pt += size

  # always align stack frame sizes to 8 byte, so that we know frames start at
  # an 8-byte boundary
  pt = align(pt, 8)

  let needsFramePointer = c.offsets.len > 0

  bu.keepTree tree:
    bu.keep(tree)
    bu.add Node(kind: Immediate, val: pt.uint32)
    bu.skip(tree)
    bu.forEach tree, n:
      bu.keepTree tree:
        if needsFramePointer:
          # append the frame pointer as a parameter to each block
          bu.append tree:
            bu.add toNode(c.addrType)
          c.framePointer = tree.len(tree.child(n, 0)).uint32
        else:
          bu.keep(tree)

        bu.keep(tree) # keep the list of locals
        bu.skip(tree) # remove the slots
        for it in 3..<tree.len(n) - 1:
          c.lowerStmt(tree, bu)

        if needsFramePointer:
          c.lowerExit(tree, bu)
        else:
          bu.keep(tree)

proc lower*(tree; ptrSize: Positive): Changeset[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = PassCtx(types: tree.child(0))
  var bu = initCursor[NodeKind](tree)

  block search:
    # search for a type to use as the address type
    for i, it in tree.pairs(c.types):
      if tree[it].kind == UInt and tree[it, 0].imm.int == ptrSize:
        c.addrType = TypeId(i)
        break search

    # we need to create a type first
    c.addrType = tree.len(c.types).TypeId

  if tree.len(c.types) == c.addrType.int:
    # create a suitable address type:
    bu.append tree:
      bu.subTree UInt:
        bu.add Node(kind: Immediate, val: ptrSize.uint32)
  else:
    bu.keep(tree) # don't modify the type list

  bu.keep(tree)
  bu.forEach tree, n:
    c.lowerProc(tree, bu)

  result = toChangeset(bu)
