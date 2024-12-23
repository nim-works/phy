## Implements a simpler disassembler for VM modules. The text representation
## can be passed back into the assembler.

import
  std/[
    intsets,
    strformat
  ],
  vm/[
    vmenv,
    vmmodules,
    vmspec,
    vmtypes,
    utils
  ]

template toOpenArray[T; I: Ordinal](s: seq[T], sl: Slice[I]): untyped =
  s.toOpenArray(sl.a.int, sl.b.int)

template toOpenArray[T; I: Ordinal](s: seq[T], sl: HOslice[I]): untyped =
  s.toOpenArray(sl.a.int, sl.b.int - 1)

proc formatValue(result: var string, t: TypeId, specifier: string) =
  result.add 't'
  result.addInt(t.int)

proc formatValue(result: var string, v: TypedValue, specifier: string) =
  case v.typ
  of vtInt:   result.addInt v.val.intVal
  of vtFloat: result.addFloat v.val.floatVal
  of vtRef:   unreachable()

proc formatValue(result: var string, t: ValueType, specifier: string) =
  case t
  of vtInt:   result.add "int"
  of vtFloat: result.add "float"
  of vtRef:   result.add "ref"


proc disassemble*(env: VmModule, prc: ProcHeader, result: var string) =
  ## Turns the given `prc` into its text representation, appending the result
  ## to `result`.
  # emit all locals at the start:
  for it in prc.locals.items:
    result.add &".local lo{it - prc.locals.a} {env.locals[it]}\n"

  var targets: IntSet # all instructions with labels attached

  # gather the jump targets for all jump-like instructions:
  for i, instr in env.code.toOpenArray(prc.code).pairs:
    if instr.opcode in {opcJmp, opcBranch}:
      targets.incl i + imm32(instr).int

  # gather the jump targets for all EH instructions:
  for e in env.ehTable.toOpenArray(prc.eh):
    targets.incl e.dst.int

  for i, instr in env.code.toOpenArray(prc.code).pairs:
    if i in targets:
      # derive the label name from the local instruction position:
      result.add &".label L{i}\n"

    result.add "  " & substr($instr.opcode, 3)
    case instr.opcode
    of opcStackAlloc, opcStackFree, opcWrInt8..opcWrRef, opcLdInt8..opcLdInt64,
       opcLdImmInt, opcAddImm:
      result.add " "
      result.addInt imm32(instr)
    of opcLdImmFloat:
      result.add " "
      result.addFloat cast[float32](imm32(instr))
    of opcPopLocal, opcSetLocal, opcGetLocal:
      result.add " lo"
      result.addInt imm32(instr)
    of opcGetGlobal:
      result.add " g"
      result.addInt instr.imm32
    of opcLdConst:
      result.add " c"
      result.addInt instr.imm32
    of opcMask, opcSignExtend, opcAddChck, opcSubChck, opcUIntToFloat,
       opcFloatToUint, opcSIntToFloat, opcFloatToSInt:
      result.add " "
      result.addInt imm32_8(instr)[1]
    of opcCall:
      let (p, args) = imm32_16(instr)
      result.add fmt" p{p} {args}"
    of opcIndCall:
      let (t, args) = imm32_16(instr)
      result.add fmt" {TypeId t} {args}"
    of opcJmp:
      result.add " L"
      result.add $(i + instr.imm32.int)
    of opcBranch:
      let (a, b) = imm32_8(instr)
      result.add fmt" L{i + a.int} {b}"
    of opcYield:
      let (a, b) = imm32_16(instr)
      result.add fmt" {a} {b}"
    else:
      discard

    result.add "\n"

    # emit the .eh directive for the attached exception handler, if any
    for e in prc.eh.items:
      if env.ehTable[e].src == i.uint32:
        result.add &".eh L{env.ehTable[e].dst}\n"
        break

proc disassemble*(m: VmModule): string =
  ## Returns the text representation for the full `m`. The text representation
  ## can be re-assembled into a ``VmModule`` that has the same meaning as `m`.
  # emit the type directives:
  for i in 0..<m.types.types.len:
    let id = TypeId(i)
    result.add fmt".type t{i} ("

    proc toString(kind: TypeKind): string =
      case kind
      of tkVoid:    "void"
      of tkInt:     "int"
      of tkFloat:   "float"
      of tkForeign: "foreign"

    for i, it in parameters(m.types, id):
      if i > 0:
        result.add ", "
      result.add toString(it)

    result.add ") -> " & toString(m.types.returnType(id)) & "\n"

  # emit the constants:
  for i, val in m.constants.pairs:
    result.add &".const c{i} {val}\n"

  # emit the globals:
  for i, val in m.globals.pairs:
    result.add &".global g{i} {val.typ} {val}\n"

  # emit the procedures:
  for i, prc in m.procs.pairs:
    case prc.kind
    of pkDefault:
      result.add &".start {prc.typ} p{i}\n"
      disassemble(m, prc, result)
      result.add ".end\n"
    of pkCallback:
      # interface names are not allowed to contain '"' or other special
      # characters; escaping the string is therefore not necessary
      result.add &".import {prc.typ} p{i} \"{m.names[prc.code.a]}\"\n"
    of pkStub:
      unreachable() # not possible

  # # emit the exports:
  for e in m.exports.items:
    case e.kind
    of expGlobal:
      result.add &".export global g{e.id} \"{m.names[e.name]}\"\n"
    of expProc:
      result.add &".export proc p{e.id} \"{m.names[e.name]}\"\n"
