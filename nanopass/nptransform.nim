## Implements the auto-generation of transformers for language forms.

import std/[macros, strformat, tables]
import passes/[trees]
import nanopass/[asts, helper, nplangdef]

proc append(to: var PackedTree[uint8], i: var int, x: Metavar) =
  to.nodes[i] = TreeNode[uint8](kind: RefTag, val: uint32(x.index))
  inc i

macro transform*(src, dst: static LangDef, nterm: static string,
                 form: static int, n: untyped): untyped =
  ## Generates the transformation from the given source language form
  ## (belonging to non-terminal `nterm`) to a target language form with
  ## compatible syntax.
  # find a target language form that's a production of the non-terminal and has
  # the same shape
  # TODO: only require the same name and number of elements, using -> to fit
  #       the rest. **Edit:** really? That can easily lead to non-obvious
  #       behaviour
  var target = -1
  for it in dst.nterminals[nterm].forms.items:
    if dst.forms[it.semantic] == src.forms[form]:
      target = it.semantic
      break
  if target == -1:
    return makeError(fmt"cannot generate transformer for '{src.forms[form]}'", n)

  # important: the generated code being efficient is of major importance! Most
  # transformations will be auto-generated, and they should thus be as fast as
  # possible
  # TODO: if none of the child nodes require a processor call, memcopy the
  #       whole sub-tree
  # TODO: (bigger refactor) pass the cursor to the transformers as a var
  #       parameter, which would eliminate unnecessary tree seeking when
  #       there's many calls to fully auto-generated non-terminal processors

  let inAst = ident"in.ast"
  let to = ident"out.ast"
  let id = dst.forms[target].id.uint8
  result = newStmtList()
  # add the root node:
  let body = quote do:
    var tmp {.used.} = `inAst`.child(`n`, 0)
    let root = `to`.nodes.len.NodeIndex
    var i = `to`.nodes.len
    # the node sequence needs to be contiguous, so it's allocated upfront
    `to`.nodes.setLen(i + `inAst`.len(`n`) + 1)
    `to`.nodes[i] = TreeNode[uint8](kind: `id`, val: `inAst`[`n`].val)
    inc i

  # call the transformers and emit the nodes in one go:
  for i, it in src.forms[form].elems.pairs:
    let fromTerminal = it.typ in src.terminals
    let toTerminal = it.typ in dst.terminals
    if fromTerminal != toTerminal or
       (toTerminal and src.terminals[it.typ].typ != src.terminals[it.typ].typ):
      body.add makeError(fmt"cannot generate transformer for {src.forms[form]}", n)
      break

    let call =
      if fromTerminal:
        if src.terminals[it.typ].tag == dst.terminals[it.typ].tag:
          # just copy the node
          quote do:
            `to`.nodes[i] = `inAst`[tmp]
            inc i
        else:
          # repack with the new tag
          let tag = dst.terminals[it.typ].tag
          quote do:
            `to`.nodes[i] = TreeNode[uint8](kind: `tag`, val: `inAst`[tmp].val)
            inc i
      else:
        let append = bindSym"append"
        let op = ident"->"
        let s = newStrLitNode(it.typ)
        let d = newStrLitNode(dst.forms[target].elems[i].typ)
        quote do:
          `append`(`to`, i,
            `op`(Metavar[src, `s`](index: tmp), Metavar[dst, `d`]))

    if it.repeat:
      let bias = src.forms[form].elems.len - 1
      body.add quote do:
        for _ in 0..<(`inAst`.len(`n`) - `bias`):
          `call`
          tmp = `inAst`.next(tmp)
    else:
      body.add quote do:
        `call`
        tmp = `inAst`.next(tmp)

  result.add body
  # the callsite takes care of fitting the index to the right type
  result.add ident"root"
