## Implements the routines for post-processing ASTs produced by passes.

import nanopass/[asts]

proc resolve(ast: Tree, result: var Tree, n: NodeIndex) =
  ## Copies the AST fragment starting at `n` to `result`, resolving all
  ## indirections in the process.
  template src: untyped = ast.nodes
  template dst: untyped = result.nodes
  const size = sizeof(AstNode)

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
        if src[i].tag < RefTag:
          last += src[i].val
        elif src[i].tag == RefTag:
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

proc resolve*[L, S](ast: sink Ast[L, S], n: NodeIndex): Ast[L, S] =
  ## Returns `ast` with all indirections in the AST resolved.
  var output: Tree
  resolve(ast.tree, output, n)
  # also resolve the sub-trees referenced from records:
  for s in fields(ast.records):
    for tup in s.mitems:
      for it in fields(tup):
        when it is Production:
          let got = output.nodes.len
          resolve(ast.tree, output, it.index)
          it.index = NodeIndex(got)

  ast.tree = output
  result = ast
