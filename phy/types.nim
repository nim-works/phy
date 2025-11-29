## Implements types and procedures for representing and working with the
## source-language types.

# XXX: the idea of ``SemType`` is misguided. Instead of using a custom IR, it
#      would be simpler *and* more efficient to use the ouput ``PackedTree`` as
#      the type IR. There's no ``SemType``-to-tree translation step then, and
#      instead of copying around ``SemType``s (which is costly), only a
#      ``NodeIndex`` (referring to the type) would have to be copied around.
#
#      If types are de-duplicated on creation, this would also reduce testing
#      types for equality to an integer comparison

type
  SizeUnit* = int
    ## Used for numbers that represent size and alignment values.
    ## 1 size-unit = 1 byte.
  # TODO: make the type a distinct unsigned type

  TypeKind* = enum
    tkError
    tkVoid
    tkUnit
    tkBool
    tkChar  ## UTF-8 byte
    tkInt
    tkFloat
    tkPointer ## polymorphic pointer type. It's only meant for
              ## internal usage
    tkArray
    tkTuple ## an anonymous product type
    tkRecord
    tkUnion ## an anonymous sum type
    tkProc
    tkSeq

  SemType* = object
    ## Represents a source-language type. The "Sem" prefix is there to prevent
    ## name conflicts with other types named `Type`.
    case kind*: TypeKind
    of tkError, tkVoid, tkUnit, tkBool, tkChar, tkInt, tkFloat, tkPointer:
      discard
    of tkTuple, tkUnion, tkProc, tkSeq:
      elems*: seq[SemType]
    of tkArray:
      length*: SizeUnit ## number of elements
      elem*: seq[SemType] ## element type
      # instead of a shared-ownership ``ref``, a single-item seq is used
    of tkRecord:
      fields*: seq[tuple[name: string, typ: SemType]]
        ## the fields are always ordered lexicographically by name

const
  AggregateTypes* = {tkArray, tkTuple, tkRecord, tkUnion, tkSeq}
  ComplexTypes*   = AggregateTypes + {tkProc}
    ## non-scalar types made up of other complex or scalar types
  AllTypes*       = {low(TypeKind) .. high(TypeKind)}

proc cmp*(a, b: SemType): int =
  ## Establishes a total order for types, intended mainly for sorting them.
  ## The order does *not* imply any type-system relevant properties, such as
  ## "is subtype of".
  result = ord(a.kind) - ord(b.kind)
  if result != 0:
    return

  # same kind, compare operands
  case a.kind
  of tkError, tkVoid, tkUnit, tkBool, tkChar, tkInt, tkFloat, tkPointer:
    result = 0 # equal
  of tkTuple, tkUnion, tkProc, tkSeq:
    result = a.elems.len - b.elems.len
    if result != 0:
      return

    for i in 0..<a.elems.len:
      result = cmp(a.elems[i], b.elems[i])
      if result != 0:
        return

    result = 0 # the types are equal
  of tkArray:
    result = cmp(a.elem[0], a.elem[0])
    if result == 0:
      result =
        if   a.length > b.length: -1
        elif a.length < b.length: 1
        else: 0
  of tkRecord:
    result = a.fields.len - b.fields.len
    if result != 0:
      return
    for i in 0..<a.fields.len:
      result = cmp(a.fields[i].name, b.fields[i].name)
      if result != 0:
        return
      result = cmp(a.fields[i].typ, b.fields[i].typ)
      if result != 0:
        return

    result = 0 # the types are equal

proc errorType*(): SemType {.inline.} =
  SemType(kind: tkError)

proc prim*(kind: TypeKind): SemType {.inline.} =
  ## Returns the primitive type with the given kind.
  SemType(kind: kind)

proc procType*(ret: sink SemType): SemType =
  ## Constructs a procedure type with `ret` as the return type.
  SemType(kind: tkProc, elems: @[ret])

proc arrayType*(length: SizeUnit, elem: sink SemType): SemType =
  ## Constructs an array type.
  SemType(kind: tkArray, length: length, elem: @[elem])

proc `==`*(a, b: SemType): bool =
  ## Compares two types for equality.
  if a.kind != b.kind:
    return false

  case a.kind
  of tkError, tkVoid, tkUnit, tkBool, tkChar, tkInt, tkFloat, tkPointer:
    result = true
  of tkTuple, tkUnion, tkProc, tkSeq:
    result = a.elems == b.elems
  of tkArray:
    result = a.length == b.length and a.elem == b.elem
  of tkRecord:
    result = a.fields == b.fields

proc isSubtypeOf*(a, b: SemType): bool =
  ## Computes whether `a` is a subtype of `b`.
  if b.kind == tkError:
    true # the error type acts as a top type
  elif a.kind == tkVoid:
    # void is the subtype of all other types
    b.kind != tkVoid
  elif b.kind == tkUnion:
    b.elems.find(a) != -1
  else:
    false

proc alignment*(t: SemType): SizeUnit
proc paddedSize*(t: SemType): SizeUnit

proc size*(t: SemType): SizeUnit =
  ## Computes the size without trailing padding of a location of type `t`.
  case t.kind
  of tkVoid: unreachable()
  of tkError: 8 # TODO: return a value indicating "unknown"
  of tkUnit, tkBool, tkChar: 1
  of tkInt, tkFloat: 8
  of tkPointer, tkProc: 8 # size of a pointer
  of tkArray:
    paddedSize(t.elem[0]) * t.length
  of tkTuple:
    var s = 0
    for it in t.elems.items:
      s += size(it)
    s
  of tkRecord:
    var s = 0
    for it in t.fields.items:
      let mask = alignment(it.typ) - 1
      s = (s + mask) and not mask
      s += size(it.typ)
    s
  of tkUnion:
    var s = 0
    for it in t.elems.items:
      s = max(s, size(it))
    s + 8 # +8 for the tag
  of tkSeq:
    size(prim(tkInt)) * 2 # length + pointer

proc alignment*(t: SemType): SizeUnit =
  ## Computes the alignment requirement for a location of type `t`.
  case t.kind
  of tkVoid: unreachable()
  of tkError: 8
  of tkUnit, tkBool, tkChar: 1
  of tkInt, tkFloat: 8
  of tkPointer, tkProc: 8
  of tkArray:
    alignment(t.elem[0])
  of tkTuple:
    var a = 0
    for it in t.elems.items:
      a = max(a, alignment(it))
    a
  of tkRecord:
    var a = 0
    for it in t.fields.items:
      a = max(a, alignment(it.typ))
    a
  of tkUnion:
    var a = 0
    for it in t.elems.items:
      a = max(a, alignment(it))
    # the tag also contributes to the alignment
    max(a, alignment(prim(tkInt)))
  of tkSeq:
    alignment(prim(tkInt))

proc innerSize*(t: SemType): SizeUnit =
  ## Computes the size without padding of a union (`t`) without the tag.
  assert t.kind == tkUnion
  result = 0
  for it in t.elems.items:
    result = max(size(it), result)

proc innerAlignment*(t: SemType): SizeUnit =
  ## Computes the size without padding of a union (`t`) without the tag.
  assert t.kind == tkUnion
  result = 0
  for it in t.elems.items:
    result = max(alignment(it), result)

proc paddedSize*(t: SemType): SizeUnit =
  ## Computes the size of an array element of type `t`.
  let mask = alignment(t) - 1
  (size(t) + mask) and not mask

proc commonType*(a, b: SemType): SemType =
  ## Finds the common type between `a` and `b`, or produces an error.
  if a == b or b.isSubtypeOf(a):
    a
  elif a.isSubtypeOf(b):
    b
  else:
    errorType()

proc isTriviallyCopyable*(typ: SemType): bool =
  ## Whether a value of `typ` can be trivially copied (that is, via a
  ## single block copy).
  case typ.kind
  of tkError, tkUnit, tkBool, tkChar, tkInt, tkFloat, tkPointer, tkProc:
    true
  of tkSeq:
    false
  of tkArray:
    isTriviallyCopyable(typ.elem[0])
  of tkUnion, tkTuple:
    # trivially copyable only if all element types are
    for it in typ.elems.items:
      if not isTriviallyCopyable(it):
        return false
    true
  of tkRecord:
    for it in typ.fields.items:
      if not isTriviallyCopyable(it.typ):
        return false
    true
  of tkVoid:
    unreachable()

proc find*(typ: SemType, field: string): int =
  ## Returns the index of the field with the given name in record type `typ`,
  ## or -1 if there's no such field.
  for i, it in typ.fields.pairs:
    if it.name == field:
      return i
  result = -1
