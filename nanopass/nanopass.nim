## Implements the nanopass framework, which is a collection of macro DSLs for
## defining intermediate languages (their syntax and grammar) and passes.

# TODO:
# * implement symbol integration
# * implement types integration
# * implement meta-data support
# * add a "compiler definition" macro

import
  passes/[trees],
  nanopass/[asts, nplangdef, nplanggen, npmatch, npbuild, nppass, nppatterns]

export asts
export nppatterns.matches
export npbuild.build, npmatch.match
export nppass.pass, nppass.inpass, nppass.outpass

export nppass.genProcessor, nppass.embed
# TODO: ^^ bind the symbols; don't mix them in

template isAtom*(x: uint8): bool =
  ## The predicate required for using an uint8 as a ``PackedTree`` tag.
  x >= RefTag

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
            let pos = dst.len
            dst.setLen(pos + int(i - prev))
            copyMem(addr dst[pos], addr src[prev], int(i - prev) * size)

          stack[^1] = (i + 1, last)
          let next = src[i].val
          stack.add (next, next)
          break outer

        inc i

      if i > prev:
        # copy the rest
        let pos = dst.len
        dst.setLen(pos + int(i - prev))
        copyMem(addr dst[pos], addr src[prev], int(i - prev) * size)

      stack.shrink(stack.len - 1)
