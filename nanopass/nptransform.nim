## Implements the auto-generation of transformers for language forms.

import std/[macros, strformat, tables]
import passes/[trees]
import nanopass/[asts, helper, nplang]

type
  Morphability = enum
    None, Ambiguous, Inexact, Exact

proc canMorph(src, dst: LangInfo, a, b: SForm): Morphability =
  ## Computes whether form `a` from `src` can be morphed into `b` from `dst`.
  if a.elems.len == b.elems.len and a.name == b.name:
    result = Exact
    for i, it in a.elems.pairs:
      if it.repeat != b.elems[i].repeat:
        result = None
        break
      elif src.types[it.typ].name != dst.types[b.elems[i].typ].name:
        result = Inexact
  else:
    result = None

proc append(to: var PackedTree[uint8], i: var int, x: Metavar) =
  to.nodes[i] = TreeNode[uint8](kind: RefTag, val: uint32(x.index))
  inc i

macro transform*(src, dst: static LangInfo, nterm: static string,
                 form: static int, input, output: PackedTree[uint8],
                 n: untyped): untyped =
  ## Generates the transformation from the given source language form
  ## to a compatible target language production of the non-terminal with
  ## name `nterm`.
  # find a target language form that's a production of the non-terminal and a
  # suitable morph target. Exact matches are preferred
  var target = -1
  var morphability = None
  for it in dst.types[dst.map[nterm]].forms.items:
    let m = canMorph(src, dst, src.forms[form], dst.forms[it])
    case m
    of None, Ambiguous:
      discard "nothing to do"
    of Inexact:
      case morphability
      of Inexact:
        morphability = Ambiguous
      of Exact, Ambiguous:
        discard "keep as is"
      of None:
        morphability = Inexact
        target = it
    of Exact:
      morphability = m
      target = it

  template formatValue(to: var string, x: SForm, prec: string) =
    to.add render(src, x)

  if morphability in {None, Ambiguous}:
    return makeError(fmt"cannot generate transformer for '{src.forms[form]}'", n)

  # important: the generated code being efficient is of major importance! Most
  # transformations will be auto-generated, and they should thus be as fast as
  # possible
  # TODO: if none of the child nodes require a processor call, memcopy the
  #       whole sub-tree
  # TODO: (bigger refactor) pass the cursor to the transformers as a var
  #       parameter, which would eliminate unnecessary tree seeking when
  #       there's many calls to fully auto-generated non-terminal processors

  let id = dst.forms[target].ntag.uint8
  result = newStmtList()
  # add the root node:
  let body = quote do:
    var tmp {.used.} = `input`.child(`n`, 0)
    let root = `output`.nodes.len.NodeIndex
    var i = `output`.nodes.len
    # the node sequence needs output be contiguous, so it's allocated upfront
    `output`.nodes.setLen(i + `input`.len(`n`) + 1)
    `output`.nodes[i] = TreeNode[uint8](kind: `id`, val: `input`[`n`].val)
    inc i

  # call the transformers and emit the nodes in one go:
  for i, a in src.forms[form].elems.pairs:
    let b = dst.forms[target].elems[i]
    let fromTerminal = src.types[a.typ].terminal
    let toTerminal   = dst.types[b.typ].terminal
    if fromTerminal != toTerminal or
       (toTerminal and src.types[a.typ].name != dst.types[b.typ].name):
      body.add makeError(fmt"cannot generate transformer for '{src.forms[form]}'", n)
      break

    let call =
      if fromTerminal:
        if src.types[a.typ].ntag == dst.types[b.typ].ntag:
          # just copy the node
          quote do:
            `output`.nodes[i] = `input`[tmp]
            inc i
        else:
          # repack with the new tag
          let tag = dst.types[b.typ].ntag
          quote do:
            `output`.nodes[i] = TreeNode[uint8](kind: `tag`, val: `input`[tmp].val)
            inc i
      else:
        let append = bindSym"append"
        let op = ident"->"
        let s = newStrLitNode(src.types[a.typ].name)
        let d = newStrLitNode(dst.types[b.typ].name)
        quote do:
          `append`(`output`, i,
            `op`(Metavar[src, `s`](index: tmp), Metavar[dst, `d`]))

    if a.repeat:
      let bias = src.forms[form].elems.len - 1
      body.add quote do:
        for _ in 0..<(`input`.len(`n`) - `bias`):
          `call`
          tmp = `input`.next(tmp)
    else:
      body.add quote do:
        `call`
        tmp = `input`.next(tmp)

  result.add body
  # the callsite takes care of fitting the index to the right type
  result.add ident"root"
