## Implements the nanopass framework, which is a collection of macro DSLs for
## defining intermediate languages (their syntax and grammar) and passes.

# TODO:
# * implement symbol integration
# * implement types integration
# * implement meta-data support
# * add a "compiler definition" macro

import
  passes/[trees],
  nanopass/[asts, nplanggen, npmatch, npbuild, nppass, nppatterns, npsexpr]

export asts
export nppatterns.matches
export npbuild.build, npmatch.match, npsexpr.renderer
export nppass.pass, nppass.inpass, nppass.outpass

export nppass.genProcessor
# TODO: ^^ bind the symbols; don't mix them in

macro defineLanguage*(name, body: untyped) =
  ## Creates a language definition and binds it to a const symbol with the
  ## given name.
  defineLanguageImpl(name, nil, body)

macro defineLanguage*(name, base, body: untyped) =
  ## Creates a language definition, extending `base`, and binds it to a const
  ## symbol with the given name. Extension doesn't imply a direction in this
  ## context.
  defineLanguageImpl(name, base, body)

proc finish*(ast: PackedTree[uint8], n: NodeIndex): PackedTree[uint8] =
  ## Returns `ast` with all indirections resolved.
  # TODO: don't export the procedure
  template src: untyped = ast.nodes
  template dst: untyped = result.nodes
  const size = sizeof(TreeNode[uint8])

  template append(start, fin: uint32) =
    let pos = dst.len
    let num = int(fin - start)
    dst.setLen(pos + num)
    copyMem(addr dst[pos], addr src[start], num * size)

  # search for runs of contiguous nodes. When encountering an indirection,
  # copy the run and move the source cursor to the indirection's
  # target; repeat.
  var stack = @[(uint32(n), uint32(n))]
  while stack.len > 0:
    block outer:
      var (i, last) = stack[^1]
      let prev = i
      while i <= last:
        if src[i].kind < RefTag:
          last += src[i].val
        elif src[i].kind == RefTag:
          if i > prev:
            # copy everything we got so far
            append(prev, i)

          stack[^1] = (i + 1, last)
          let next = src[i].val
          stack.add (next, next)
          break outer

        inc i

      if i > prev:
        # copy the rest
        append(prev, i)

      stack.shrink(stack.len - 1)
