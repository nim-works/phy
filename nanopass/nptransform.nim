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

proc append(to: var PackedTree[uint8], i: var int,
            tag: uint8, val: uint32) {.inline.} =
  to.nodes[i] = TreeNode[uint8](kind: tag, val: val)
  inc i

macro transform*(src, dst: static LangInfo, nterm: static string,
                 form: static int, input, output: PackedTree[uint8],
                 cursor: untyped): untyped =
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
    return
      makeError(fmt"cannot generate transformer for '{src.forms[form]}'", cursor)

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
    let len = `input`.len(pos(`cursor`))
    discard enter(`input`, `cursor`)
    let root = `output`.nodes.len.NodeIndex
    var i = `output`.nodes.len
    # the node sequence has to be contiguous, so it's allocated upfront
    `output`.nodes.setLen(i + len + 1)
    `output`.nodes[i] = TreeNode[uint8](kind: `id`, val: uint32(len))
    inc i

  # call the transformers and emit the nodes in one go:
  for i, a in src.forms[form].elems.pairs:
    let b = dst.forms[target].elems[i]
    let s = ident(src.types[a.typ].mvar)
    let d = ident(dst.types[b.typ].mvar)
    let got =
      case src.types[a.typ].kind
      of tkTerminal:
        quote do:
          src.`s`(index: `input`[pos(`cursor`)].val)
      of tkRecord:
        quote do:
          src.`s`(id: `input`[pos(`cursor`)].val)
      of tkNonTerminal:
        quote do:
          src.`s`(index: get(`input`, `cursor`))

    let append = bindSym"append"
    let call =
      case dst.types[b.typ].kind
      of tkTerminal:
        let tag = dst.types[b.typ].ntag
        quote do:
          `append`(`output`, i, uint8(`tag`), (`got` -> dst.`d`).index)
      of tkRecord:
        let tag = dst.types[b.typ].rtag
        quote do:
          `append`(`output`, i, uint8(`tag`), (`got` -> dst.`d`).id)
      of tkNonTerminal:
        quote do:
          `append`(`output`, i, RefTag, (`got` -> dst.`d`).index.uint32)

    if a.repeat:
      let bias = src.forms[form].elems.len - 1
      body.add quote do:
        for _ in 0..<(len - `bias`):
          `call`
          advance(`input`, `cursor`)
    else:
      body.add quote do:
        `call`
        advance(`input`, `cursor`)

  result.add body
  # the callsite takes care of fitting the index to the right type
  result.add ident"root"

macro transformType*(src, dst: static LangInfo, nterm: static string,
                     typ: static int, input, output: PackedTree[uint8],
                     cursor: untyped): untyped =
  ## Transforms the instance of type `typ` (may be either a terminal or non-
  ## terminal) at `cursor` to an AST fitting the destination non-terminal
  ## `nterm` and appends the result to `output`.
  proc contains(lang: LangInfo, typ: LangType, search: int): bool =
    for it in typ.sub.items:
      result = it == search
      if not result and lang.types[it].kind == tkNonTerminal:
        result = contains(lang, typ, search)
      if result:
        break

  let smvar = ident(src.types[typ].mvar)
  let got =
    case src.types[typ].kind
    of tkTerminal:
      quote do:
        src.`smvar`(index: `input`[get(`input`, `cursor`)].val)
    of tkRecord:
      quote do:
        src.`smvar`(id: `input`[get(`input`, `cursor`)].val)
    of tkNonTerminal:
      quote do:
        src.`smvar`(index: get(`input`, `cursor`))

  let dtyp = dst.map.getOrDefault(src.types[typ].name, -1)

  # prefer a direct processor (i.e. 'a -> a') over 'a -> b'
  if dtyp != -1 and contains(dst, dst.types[dst.map[nterm]], dtyp):
    let dmvar = ident(dst.types[dtyp].mvar)
    case dst.types[dtyp].kind
    of tkTerminal:
      # a new node needs to be allocated so that a reference to it can
      # be returned
      let tag = dst.types[dtyp].ntag.uint8
      let tmp = genSym()
      result = quote do:
        let `tmp` = `got` -> dst.`dmvar`
        `output`.nodes.add TreeNode[uint8](kind: `tag`, val: `tmp`.index)
        NodeIndex(`output`.nodes.high)
    of tkRecord:
      # a new node needs to be allocated so that a reference to it can
      # be returned
      let tag = dst.types[dtyp].rtag.uint8
      let tmp = genSym()
      result = quote do:
        let `tmp` = `got` -> dst.`dmvar`
        `output`.nodes.add TreeNode[uint8](kind: `tag`, val: `tmp`.id)
        NodeIndex(`output`.nodes.high)
    of tkNonTerminal:
      result = quote do:
        (`got` -> dst.`dmvar`).index
  else:
    # no direct processor is possible; use an indirect processor
    let dmvar = ident(dst.types[dst.map[nterm]].mvar)
    result = quote do:
      (`got` -> dst.`dmvar`).index

template transformRecord*(rec: tuple, to: typedesc[tuple]): untyped =
  ## Transforms the given record `rec` into a target-language record with
  ## internal type `to`.
  var dest: to
  for dname, dval in fieldPairs(dest):
    var found {.global, compileTime.} = false
    for sname, sval in fieldPairs(rec):
      when dname == sname:
        dval = sval -> typeof(dval)
        static: found = true

    # truncating is possible and allowed, but widening is not
    when not found:
      {.error: "source record is missing a field called '" & dname & "'".}

  dest
