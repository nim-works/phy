## Turns `At` and `Field` expressions into flat `Path` expressions, for easier
## processing by later passes (|L5| -> |L4|).

import
  std/[tables],
  passes/[changesets, syntax, trees],
  vm/utils

type
  Node = TreeNode[NodeKind]
  TypeId = distinct uint32

  Context = object
    args: seq[VirtualTree]
      ## re-used throughout the pass in order to reduce allocator activity
    locals: NodeIndex

using
  c: var Context
  tree: PackedTree[NodeKind]
  n: NodeIndex
  bu: var ChangeSet[NodeKind]

func typ(n: Node): TypeId =
  assert n.kind == Type
  TypeId(n.val)

func resolve(tree; typ: TypeId): NodeIndex =
  tree.child(tree.child(0), typ.ord)

proc typeof(c; tree; n): NodeIndex =
  case tree[n].kind
  of Local: tree.child(c.locals, tree[n].val)
  of Deref: tree.child(n, 0)
  else:     unreachable()

proc lookupField(tree; typ: NodeIndex, field: int): NodeIndex =
  case tree[typ].kind
  of Record: tree.child(tree.child(typ, field + 2), 1)
  of Union:  tree.child(typ, field + 2)
  else:      unreachable()

proc lower(c; tree; n; bu) =
  proc gather(c; tree; n; bu): NodeIndex {.nimcall.} =
    ## Recurses through a chain of path operations, processes and adds their
    ## index operands to the `args` list, and returns the final type.
    case tree[n].kind
    of Field:
      let (a, b) = tree.pair(n)
      result = gather(c, tree, a, bu)
      result = lookupField(tree, tree.resolve(tree[result].typ),
                           tree[b].val.int)
      c.args.add toVirtual(tree.child(n, 1))
    of At:
      let (a, b) = tree.pair(n)
      result = gather(c, tree, a, bu)
      result = tree.child(tree.resolve(tree[result].typ), 3)
      let v = bu.openTree(tree, b, c.lower(tree, b, bu))
      c.args.add v
    of Deref:
      result = tree.child(n, 0)
      let v = bu.openTree(tree, n, c.lower(tree, n, bu))
      c.args.add v
    of Local:
      result = c.typeof(tree, n)
      c.args.add toVirtual(n)
    else:
      unreachable()

  for it in tree.filter(n, {Field, At}):
    let start = c.args.len
    let x = gather(c, tree, it, bu)
    # prepend the type node to the start of the operands:
    c.args.insert toVirtual(x), start

    bu.replace it, bu.newTree(Path, c.args.toOpenArray(start, c.args.high))
    c.args.shrink(start)

proc lower*(tree): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`).
  var c = Context()

  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      let (_, locals, body) = tree.triplet(it)

      c.locals = locals
      c.lower(tree, body, result)
