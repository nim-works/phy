## Lowers |L1| into |L0|. This means:
## * turning locals of ``Blob`` type into local pointers
## * computing the stack-space required for each continuation

import
  std/[tables],
  passes/[builders, changesets, spec, trees]

type
  Node = TreeNode[NodeKind]

using
  tree: PackedTree[NodeKind]

func typ(n: Node): int =
  assert n.kind == Type
  result = n.val.int

func id(n: Node): int =
  result = n.val.int

proc lower(c: var ChangeSet[NodeKind], tree; n: NodeIndex) =
  ## Computes the changeset representing the lowering for a procedure (`n`).
  var locals = initTable[int, int]() ## local ID -> stack upper-bound

  # compute the stack layout and the locals in stack memory and emit the
  # address initialization
  var stack = 0
  for i, it in tree.pairs(tree.child(n, 1)):
    let typ = tree.child(tree.child(0), tree[it].typ)
    if tree[typ].kind == Blob:
      # the blob local is turned into an address local storing the real
      # address. The address is assigned at the very start of the
      # procedure
      # TODO: assign the address in the first continuation that uses the local.
      #       This reduces run-time overhead when the local is not used
      c.insert(tree, tree.child(tree.child(n, 2), 0), 2, Asgn):
        bu.add Node(kind: Local, val: i.uint32)
        bu.subTree(Addr):
          bu.add Node(kind: IntVal, val: stack.uint32)

      stack += tree[typ, 0].val.int
      locals[i] = stack

  # TODO: make the stack allocator smarter. Take into account which locals are
  #       alive at the same time. For example, if two blob locals are never
  #       alive concurrently, they can re-use the same memory region

  for it in tree.items(tree.child(n, 2)):
    if tree.len(it) > 1:
      # compute the maximum amount of stack space required:
      var maxStack = 0
      for it in tree.items(tree.child(it, 1)):
        maxStack = max(maxStack, locals.getOrDefault(tree[it].id, 0))

      # replace the list of locals with the required stack space:
      c.replace(tree.child(it, 1), Node(kind: Immediate, val: maxStack.uint32))

      # ``(Addr (Local x))`` -> ``(Copy (Local x))``
      for it in tree.flat(it):
        if tree[it].kind == Addr:
          c.replace(it, Copy):
            bu.add tree[it, 0]

proc lower*(tree; ptrSize: int): ChangeSet[NodeKind] =
  ## Computes the changeset representing the lowering for a whole module
  ## (`tree`). `ptrSize` is the size-in-bytes of a pointer value.

  # lower the blob types. They're turned into pointer types
  for it in tree.items(tree.child(0)):
    if tree[it].kind == Blob:
      # TODO: re-use a single pointer type, though this will require patching
      #       all used types. It might be better to introduce a ``None`` type,
      #       and leave mapping type IDs to ``pass0``
      result.replace(it, UInt):
        bu.add Node(kind: Immediate, val: uint32 ptrSize)

  # lower the procedures:
  for it in tree.items(tree.child(2)):
    if tree[it].kind == ProcDef:
      lower(result, tree, it)
