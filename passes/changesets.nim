## This module implements the `ChangeSet <#ChangeSet>`_ API, which is an
## efficient way to modify the packed trees. The underlying idea is to:
## * separate modifying the tree from computing the modification
## * only modify what's necessary instead of rebuilding the whole tree
##
## The nodes or subtrees to insert or replace other subtrees with are
## represented by `virtual trees <#VirtualTree>`_, and there are multiple
## ways to create them:
## * with a `Builder` (see `buildTree <#buildTree.t,ChangeSet[T],T,untyped>`_)
## * with the `buildTree <#buildTree.m,ChangeSet[T],TreeOperand>`_ macro
## * manually via `newTree <#newTree,ChangeSet[T],T,varargs[VirtualTree]>`_
## * by "capturing" modifications via
##   `openTree <#openTree.t,ChangeSet[T],PackedTree[T],NodeIndex,untyped>`_
##
## Virtual trees can only be used with the changeset they were created with.

#[
Notes on the implementation:
* changesets are implemented as instructions driving a mini-VM that copies
  nodes from the source and changeset buffers into an output buffer
* virtual trees created through the changeset are reusable VM subroutines
* when recording a modification, the modification is first added to a staging
  action buffer. Actions are then compiled into instructions when finishing a
  capture (`openTree`) or applying the changeset
]#

import
  std/[algorithm, macros],
  passes/trees

type
  Opcode = enum
    Ret      ## return from the active subroutine
    Call     ## enter a subroutine
    SetSrc   ## set the source buffer cursor position
    SetTmp   ## set the changeset buffer cursor position
    CopySrc  ## copy N nodes from the source buffer
    CopyTmp  ## copy N nodes from the changeset buffer
    CopyTree ## copy the subtree from the given source buffer position

  Mode = enum
    ## Describes how an action affects the source buffer cursor
    ## position. The enum order is significant.
    Insert  ## don't modify the cursor position
    Single  ## skip over a single node, even if the root of a subtree
    Replace ## skip over the subtree

  ChangeSet*[T] = object
    nodes: seq[TreeNode[T]]
      ## the changeset node buffer, storing all changeset-created nodes
    code: seq[tuple[op: Opcode, arg: uint32]]
      ## the final code of all subroutines
    actions: seq[tuple[src: NodeIndex, prog: uint32, mode: Mode]]
      ## the not-yet-sorted staged actions

  VirtualTree* = object
    ## A lightweight handle for a subtree.
    case isRef: bool
    of true:
      n: NodeIndex
    of false:
      prog: uint32

  TreeRef* = object
    ## Refers to some source subtree that is open for modification.
    diff: int ## counts the child node additions/removals

  TreeOperand = distinct bool
    ## Helper type for the macro-based tree building API.

template toVirtual*(x: NodeIndex): VirtualTree =
  ## Creates a virtual tree referring to `x`. This is a very low-cost
  ## operation.
  VirtualTree(isRef: true, n: x)

func newTree*[T](c: var ChangeSet[T], kind: T,
                 children: varargs[VirtualTree]): VirtualTree =
  ## Creates and returns a new subtree with kind `kind` and the given
  ## `children`.
  result = VirtualTree(isRef: false, prog: c.code.len.uint32)

  c.code.add (SetTmp, c.nodes.len.uint32)
  c.code.add (CopyTmp, 1'u32)
  c.nodes.add TreeNode[T](kind: kind, val: children.len.uint32)
  for it in children.items:
    if it.isRef:
      c.code.add (CopyTree, it.n.ord.uint32)
    else:
      c.code.add (Call, it.prog)

  c.code.add (Ret, 0'u32)

template buildTree*[T](c: var ChangeSet[T], k: T, body: untyped): VirtualTree =
  ## Sets up a ``Builder`` instance and makes it available to `body`. Returns a
  ## virtual tree created out of the tree constructed with the builder.
  mixin initBuilder, finish, subTree
  if true:
    let start = c.nodes.len
    var bu {.inject.} = initBuilder(move c.nodes)
    subTree bu, k:
      body

    c.nodes = finish(bu)
    let cl = c.code.len
    c.code.add (SetTmp, start.uint32)
    c.code.add (CopyTmp, uint32(c.nodes.len - start))
    c.code.add (Ret, 0'u32)
    VirtualTree(isRef: false, prog: cl.uint32)
  else:
    raise AssertionDefect.newException("") # mark as unreachable

proc replace*[T](c: var ChangeSet[T], at: NodeIndex, with: TreeNode[T]) =
  ## Replaces the subtree at `at` with `with`.
  c.nodes.add with
  c.actions.add (at, c.code.len.uint32, Replace)
  c.code.add (SetTmp, c.nodes.high.uint32)
  c.code.add (CopyTmp, 1'u32)
  c.code.add (Ret, 0'u32)

proc replace*[T](c: var ChangeSet[T], at: NodeIndex, with: VirtualTree) =
  ## Replaces the subtree at `at` with `with`.
  # do nothing when a subtree is attempted to be replaced with itself
  if not with.isRef or at.ord != with.n.ord:
    if with.isRef:
      c.actions.add (at, c.code.len.uint32, Replace)
      c.code.add (CopyTree, with.n.ord.uint32)
      c.code.add (Ret, 0'u32)
    else:
      c.actions.add (at, with.prog, Replace)

template replace*[T](c: var ChangeSet[T], n: NodeIndex, kind: T,
                     body: untyped) =
  replace(c, n, buildTree(c, kind, body))

proc remove*[T](c: var ChangeSet[T], parent: var TreeRef, at: NodeIndex) =
  ## Removes the child node of parent at `at`.
  dec parent.diff
  c.actions.add (at, c.code.len.uint32, Replace)
  c.code.add (Ret, 0'u32)

proc insert*[T](c: var ChangeSet[T], parent: var TreeRef, at: NodeIndex,
                n: VirtualTree) =
  ## Adds `n` as an direct children of `parent`. `at` must be the position of a
  ## subtree of `parent`.
  inc parent.diff
  if n.isRef:
    c.actions.add (at, c.code.len.uint32, Insert)
    c.code.add (CopyTree, n.n.ord.uint32)
    c.code.add (Ret, 0'u32)
  else:
    c.actions.add (at, n.prog, Insert)

proc insert*[T](c: var ChangeSet[T], parent: var TreeRef, at: NodeIndex,
                n: TreeNode[T]) =
  ## Adds `n` as a direct children of `parent`. `at` must be the node index
  ## of one of `parent`'s direct child nodes.
  inc parent.diff
  c.nodes.add n
  c.actions.add (at, c.code.len.uint32, Insert)
  c.code.add (SetTmp, c.nodes.high.uint32)
  c.code.add (CopyTmp, 1'u32)
  c.code.add (Ret, 0'u32)

proc compile[T](c: var ChangeSet[T], tree: PackedTree[T], start: int,
                first, limit: NodeIndex): uint32 =
  ## Compiles the staged actions with an index >= `start` into a subroutine,
  ## returning the subroutine's start position. `first` and `limit` is the span
  ## of source buffer nodes in whose context to compile the program.

  # sort the actions by affected node position, with the action kind as the
  # second order (e.g., insertions take place before replacements). It's
  # important that the sorting is stable
  sort(c.actions.toOpenArray(start, c.actions.high), proc(a, b: auto): int =
    result = a.src.ord - b.src.ord
    if result == 0:
      result = a.mode.ord - b.mode.ord
  )

  result = c.code.len.uint32 # the start of the subroutine

  # all nodes in-between the modified subtrees are taken from the source
  # buffer

  var prev = first.ord
  for (pos, prog, mode) in c.actions.toOpenArray(start, c.actions.high).items:
    # if the assertion below fails, it means that multiple actions
    # modify parts of the same subtree, which is not supported
    assert prev <= pos.ord, "overlapping actions found"
    if prev < pos.ord:
      c.code.add (SetSrc, prev.uint32)
      c.code.add (CopySrc, uint32(pos.ord - prev))

    if c.code[prog].op == Ret:
      discard "omit the no-op call"
    elif c.code[prog + 1].op == Ret:
      # inline the call
      c.code.add c.code[prog]
    else:
      # cannot inline; call the subroutine
      c.code.add (Call, prog)

    prev =
      case mode
      of Insert:  pos.ord
      of Single:  pos.ord + 1
      of Replace: tree.next(pos).ord

  if prev < ord(limit):
    # copy the remaining nodes from the source buffer
    c.code.add (SetSrc, prev.uint32)
    c.code.add (CopySrc, uint32(limit.ord - prev))

  c.actions.shrink(start)

proc closeTree[T](c: var ChangeSet[T], tree: PackedTree[T], start, diff: int,
                  n: NodeIndex, kind: T): VirtualTree =
  if start == c.actions.len:
    # nothing was changed, return a normal reference
    VirtualTree(isRef: true, n: n)
  else:
    let pos = c.code.len.uint32
    var first = n.ord
    if diff != 0 or kind != tree[n].kind:
      # reduce interruptions to block copies by only modifying the root node
      # if something changes
      c.nodes.add TreeNode[T](kind: kind, val: uint32(tree[n].val.int + diff))
      c.code.add (SetTmp, c.nodes.high.uint32)
      c.code.add (CopyTmp, 1'u32)
      first += 1

    discard compile(c, tree, start, NodeIndex(first), tree.next(n))
    c.code.add (Ret, 0'u32)
    VirtualTree(isRef: false, prog: pos)

proc closeTree[T](c: var ChangeSet[T], tree: PackedTree[T], start, diff: int,
                  n: NodeIndex): VirtualTree {.inline.} =
  closeTree(c, tree, start, diff, n, tree[n].kind)

template openTree*[T](c: var ChangeSet[T], tree: PackedTree[T], n: NodeIndex,
                      body: untyped): VirtualTree =
  ## Captures all modifications of subtree `n` recorded within body into a
  ## virtual tree. If the returned virtual tree is not used anywhere, the
  ## modifications won't appear in the output when applying the changeset.
  if true:
    let start = c.actions.len
    body
    closeTree(c, tree, start, 0, n)
  else:
    raise AssertionDefect.newException("") # make the compiler happy

template openTree*[T](c: var ChangeSet[T], tree: PackedTree[T], n: NodeIndex,
                      parent, body: untyped): VirtualTree =
  ## Captures all modifications of subtree `n` recorded within body into a
  ## virtual tree. Direct child subtrees can be removed or inserted through
  ## the injected `parent` variable.
  if true:
    let start = c.actions.len
    var parent = TreeRef()
    body
    closeTree(c, tree, start, parent.diff, n)
  else:
    raise AssertionDefect.newException("") # make the compiler happy

template modifyTree*[T](c: var ChangeSet[T], tree: PackedTree[T], n: NodeIndex,
                        parent, body: untyped) =
  ## Opens the subtree at `n` for modification, allowing for inserting or
  ## removing child nodes from `n` through `parent`.
  if true:
    let start = c.actions.len
    var parent = TreeRef()
    body
    c.replace n, closeTree(c, tree, start, parent.diff, n)

template modifyTree*[T](c: var ChangeSet[T], tree: PackedTree[T], n: NodeIndex,
                        kind: T, parent, body: untyped) =
  ## Opens the subtree at `n` for modification, allowing for inserting or
  ## removing child nodes from `n`. The kind of `n` is changed to `kind`.
  if true:
    let start = c.actions.len
    var parent = TreeRef()
    body
    c.replace n, closeTree(c, tree, start, parent.diff, n, kind)

# the macro-based API follows. In order to keep the implementation simple, as
# much validation / type checking as is sensible is left to the compiler. This
# also makes the macro more robust against macro breakage and/or changes.

proc tree*[T](kind: T, args: varargs[TreeOperand]): TreeOperand =
  discard "exists only for the macro"

proc node*[T](x: TreeNode[T]): TreeOperand =
  discard "exists only for the macro"

template node*[T](k: T, v: uint32): TreeOperand =
  node(TreeNode[T](kind: k, val: v))

proc embed*(t: VirtualTree): TreeOperand =
  ## Embeds an existing virtual tree.
  discard "exists only for the macro"

template embed*(n: NodeIndex): TreeOperand =
  embed(toVirtual n)

# disable checks and stacktraces for the procedure used by the macro. It's
# guaranteed that they don't exhibit run-time faults (unless the macro has a
# bug, of course)
{.push stacktrace: off, checks: off.}

proc setNode[T](c: var ChangeSet[T], i: int, val: TreeNode[T]) {.inline.} =
  c.nodes[i] = val

proc setOp[T](c: var ChangeSet[T], i: int, op: Opcode,
               arg: uint32) {.inline.} =
  c.code[i] = (op, arg)

proc embed[T](c: var ChangeSet[T], i: int, t: VirtualTree) {.inline.} =
  if t.isRef:
    c.code[i] = (CopyTree, t.n.ord.uint32)
  else:
    c.code[i] = (Call, t.prog)

{.pop.}

macro buildTree*[T](c: var ChangeSet[T], op: TreeOperand): VirtualTree =
  ## Creates a virtual tree from tree description `op`. The `tree`, `node`,
  ## and `embed` procedures are used for describing a tree. Side-effectful
  ## tree descriptions are supported, including operations that modify the
  ## changeset.
  # the amount of required code and nodes is statically know. They're
  # allocated up-front, which is necessary for handling the case where
  # arguments have side effects that modify the changeset (by adding nodes
  # or code)

  # separate parameters are more efficient than a single object with the
  # current NimSkull VM, hence the large parameter lists in the inner
  # procedures. Efficiency is important here

  proc appendNode(to, c, nstart: NimNode, np: var int, expr: NimNode) =
    let prc = bindSym"setNode"
    to.add quote do:
      `prc`(`c`, `nstart` + `np`, `expr`)
    inc np

  proc appendInstr(to, c, cstart: NimNode, cp: var int, op: Opcode,
                   arg: NimNode) =
    let prc = bindSym"setOp"
    to.add quote do:
      `prc`(`c`, `cstart` + `cp`, `op`, `arg`)
    inc cp

  proc process(n, to, c, nstart, cstart, typ: NimNode,
               prev, np, cp: var int) =
    # c = expression passed to the macro's `c` parameter
    # prev = previous node index offset
    # np = node index offset
    # cp = instruction index offset
    n.expectKind nnkCallKinds
    if eqIdent(n[0], "tree"):
      let
        kind = n[1]
        arr = n[2][^1] # the array constructor containing the child nodes
        len = arr.len.uint32

      to.appendNode(c, nstart, np):
        quote: TreeNode[`typ`](kind: `kind`, val: `len`)

      for j in 0..<arr.len:
        process(arr[j], to, c, nstart, cstart, typ, prev, np, cp)
    elif eqIdent(n[0], "embed"):
      if prev < np:
        # there are some staged nodes, copy them first
        to.appendInstr(c, cstart, cp, SetTmp, quote do: uint32(`nstart` + `prev`))
        to.appendInstr(c, cstart, cp, CopyTmp, newLit uint32(np - prev))
        prev = np

      # delegate figuring out which instruction to use to a non-macro
      # routine; less code to generate
      let prc = bindSym"embed"
      let val = n[1]
      to.add quote do:
        `prc`(`c`, `cstart` + `cp`, `val`)
      inc cp
    elif eqIdent(n[0], "node"):
      appendNode(to, c, nstart, np, n[1])
    else:
      error("unknown tree operand", n)

  let
    nstart = genSym("nstart")
    cstart = genSym("cstart")
    op     = if op.kind == nnkStmtListExpr: op[^1] else: op

  result = newTree(nnkStmtList)
  result.add quote do:
    let `nstart` = `c`.nodes.len
    let `cstart` = `c`.code.len
  # reserve two empty slots for the setLen calls:
  result.add newEmptyNode()
  result.add newEmptyNode()

  var
    prev = 0
    np = 0
    cp = 0

  process(op, result, c, nstart, cstart, T, prev, np, cp)

  if prev < np:
    # copy the trailing nodes:
    result.appendInstr(c, cstart, cp, SetTmp, quote do: uint32(`nstart` + `prev`))
    result.appendInstr(c, cstart, cp, CopyTmp, newLit uint32(np - prev))

  result.appendInstr(c, cstart, cp, Ret, newLit(0'u32))

  # fill in the setLen calls:
  result[1] = quote: `c`.nodes.setLen(`nstart` + `np`)
  result[2] = quote: `c`.code.setLen(`cstart` + `cp`)

  result.add quote do:
    VirtualTree(isRef: false, prog: uint32(`cstart`))

# ---- end of macro-base tree building ----

proc add[T](a: var openArray[T], p: var int, b: openArray[T]) =
  # usually faster than the built-in `add` because it doesn't copy
  # element-by-element
  copyMem(addr a[p], addr b[0], b.len * sizeof(T))
  p += b.len

func apply*[T](tree: PackedTree[T], c: sink ChangeSet[T]): PackedTree[T] =
  ## Applies the changeset `c` to `tree`, returning a new packed tree.
  let
    # compile the program for the top-level tree:
    entry = compile(c, tree, 0, NodeIndex(0), NodeIndex(tree.nodes.len))
    code  = move c.code # use a (local), for faster access

  # VM state
  var
    pc = entry
    stack: seq[uint32]

  template slice(a: int): openArray[TreeNode[T]] =
    toOpenArray(tree.nodes, a, tree.next(NodeIndex a).ord - 1)

  # first do a dry run that does no copying, but only counts the space
  # required in the output buffer. The idea is to allocate the whole output
  # buffer up-front, reducing allocator activity and eliminating resize-induced
  # copies
  var total = 0
  while pc < code.len.uint32:
    let (op, arg) = code[pc]
    case op
    of Ret:
      pc = stack.pop()
    of Call:
      stack.add pc
      pc = arg
      continue
    of SetSrc, SetTmp:
      discard
    of CopySrc, CopyTmp:
      total += arg.int
    of CopyTree:
      total += slice(arg.int).len

    inc pc

  # re-run the program, but now do the actual copying
  pc = entry

  var
    nodes: seq[TreeNode[T]] ## output node buffer
    sp = 0 ## cursor into source buffer
    tp = 0 ## cursor into changeset node buffer
    dest = 0 ## cursor into output buffer

  nodes.newSeq(total)
  while pc < code.len.uint32:
    let (op, arg) = code[pc]
    case op
    of Ret:
      pc = stack.pop()
    of Call:
      stack.add pc
      pc = arg
      continue
    of SetSrc:
      sp = arg.int
    of SetTmp:
      tp = arg.int
    of CopySrc:
      let p = sp + arg.int
      nodes.add(dest, tree.nodes.toOpenArray(sp, p - 1))
      sp = p
    of CopyTmp:
      let p = tp + arg.int
      nodes.add(dest, c.nodes.toOpenArray(tp, p - 1))
      tp = p
    of CopyTree:
      nodes.add(dest, slice(arg.int))

    inc pc

  result = initTree(nodes, tree.literals)
