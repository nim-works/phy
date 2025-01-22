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

proc apply*(body: var MirBody, env: var MirEnv) =
  var c = initChangeset(body)
  liftStrings(body.code, env, c)
  apply(body, c)
