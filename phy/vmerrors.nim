## Implements to-text rendering for VM validation errors.

import
  std/[
    options,
    streams,
    strformat
  ],
  vm/[
    disasm,
    vmenv,
    vmmodules,
    vmvalidation
  ]

proc renderStack(to: Stream, stack: openArray[ValueType], isTruncated: bool) =
  ## Renders the operand stack `stack` to text and writes it to `to`.
  to.write "["
  if isTruncated:
    to.write "..."

  for i, it in stack.pairs:
    if i > 0 or isTruncated:
      to.write ", "

    to.write:
      case it
      of vtInt: "int"
      of vtFloat: "float"
      of vtRef: "ref"

  to.write "]"

proc render*(to: Stream, p: ErrPayload) =
  ## Renders the payload to text and writes it to `to`.
  case p.kind
  of ekGeneric:
    to.write(p.msg)
  of ekStack:
    to.write("expected operand stack with shape ")
    to.renderStack(p.expected, not p.full)
    to.write(", but got ")
    if p.got.len < p.expected.len or p.full:
      to.renderStack(p.got, false)
    else:
      to.renderStack(
        toOpenArray(p.got, p.got.len - p.expected.len, p.got.high), true)

proc surrounding(i: uint32, num: int, bounds: Slice[uint32]): Slice[int] =
  ## Computes the slice with maximum size `num` that includes `i` and that's
  ## contained within `bounds`, with `i` being preferred to be in the middle.
  let start = int(i) - (num div 2)
  let dist = num - 1
  if start < bounds.a.int:
    bounds.a.int .. min(bounds.a.int + dist, bounds.b.int)
  elif start + dist > bounds.b.int:
    max(bounds.a.int, bounds.b.int - dist) .. bounds.b.int
  else:
    start .. (start + dist)

proc render*(to: Stream, module: VmModule, err: Error) =
  ## Renders `err` to text and writes it to `to`, with `module` being the
  ## module the error concerns.
  # important: keep in mind that the module may be unsound, meaning that
  # reference being valid cannot be relied upon
  case err.ctx.entity
  of entNone:
    discard "no context"
  of entProc:
    if err.ctx.instr.isSome:
      let at = err.ctx.instr.unsafeGet
      let total = module.procs[err.ctx.index].code
      to.write &"problem in procedure {err.ctx.index}:\n\n"
      # try to always show three instructions as context
      let window = surrounding(at, 3, total)
      if window.a > total.a.int:
        to.write "    ...\n"

      for i in window.items:
        var tmp = ""
        disassemble(i, module.code[i], tmp)
        to.write "  "
        if i == int(at):
          to.write "> "
        else:
          to.write "  "
        to.write tmp
        to.write "\n"

      if window.b < total.b.int:
        to.write "    ...\n"

      to.write "\n"
    else:
      to.write &"problem with header of procedure {err.ctx.index}: "
  else:
    to.write &"problem with {err.ctx.entity} {err.ctx.index}: "

  render(to, err.payload)
