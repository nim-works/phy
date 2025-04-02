## Implements some additional MIR passes for Skully.

import
  compiler/mir/[
    mirchangesets,
    mirenv,
    mirtrees,
    mirconstr,
    mirbodies,
    datatables
  ]

proc liftStrings(tree: MirTree, env: var MirEnv, changes: var Changeset) =
  for i in 0..<tree.len:
    if tree[i].kind == mnkStrLit:
      # create an anonymous constant from the literal:
      let c = toConstId env.data.getOrPut(@[tree[i]])
      # replace the usage of the literal with the anonymous constant:
      changes.replaceMulti(tree, NodePosition(i), bu):
        bu.use toValue(c, tree[i].typ)

proc moveUnscoped(tree: MirTree, changes: var Changeset) =
  ## Moves defs within `mnkIf` sections without an accompanying scope to
  ## before the if, so that the def is guaranteed to dominate all usages.
  var
    stack: seq[(int, NodePosition, LabelId)]
    depth = 0
    it = NodePosition(0)
  while it < tree.len.NodePosition:
    case tree[it].kind
    of mnkIf:
      if tree[tree.sibling(it)].kind != mnkScope:
        # found an 'if' with an unscoped body
        if stack.len == 0 or stack[^1][0] != depth:
          # make sure to move to the start of the *outermost* unscoped 'if':
          #   if ...:  # <- move to before here, not before the if below
          #     if ...:
          #       def x = ...
          stack.add (depth, it, tree[it, 1].label)
    of mnkDef, mnkDefCursor:
      if stack.len > 0 and stack[^1][0] == depth:
        # the def is part of an if and there's no scope start in-between
        # them -> move
        changes.insert(tree, stack[^1][1], it, bu):
          bu.subTree tree[it].kind:
            bu.add tree[it, 0]
            bu.add MirNode(kind: mnkNone)
        changes.changeTree(tree, it, MirNode(kind: mnkInit))
    of mnkScope:
      inc depth
    of mnkEndScope:
      dec depth
    of mnkEndStruct:
      if stack.len > 0 and stack[^1][2] == tree[it, 0].label:
        stack.shrink(stack.len - 1)
    else:
      discard

    it = tree.sibling(it)

proc apply*(body: var MirBody, env: var MirEnv) =
  var c = initChangeset(body)
  liftStrings(body.code, env, c)
  moveUnscoped(body.code, c)
  apply(body, c)
