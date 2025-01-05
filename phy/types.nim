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

import
  vm/[
    utils
  ]

type
  TypeKind* = enum
    tkError
    tkVoid
    tkUnit
    tkBool
    tkInt
    tkFloat
    tkTuple ## an anonymous product type
    tkUnion ## an anonymous sum type
    tkProc
    tkSeq

  SemType* = object
    ## Represents a source-language type. The "Sem" prefix is there to prevent
    ## name conflicts with other types named `Type`.
    case kind*: TypeKind
    of tkError, tkVoid, tkUnit, tkBool, tkInt, tkFloat:
      discard
    of tkTuple, tkUnion, tkProc, tkSeq:
      elems*: seq[SemType]

const
  AggregateTypes* = {tkTuple, tkUnion, tkSeq}
  ComplexTypes*   = AggregateTypes + {tkProc}
    ## non-primitive types

proc cmp*(a, b: SemType): int =
  ## Establishes a total order for types, intended mainly for sorting them.
  ## The order does *not* imply any type-system relevant properties, such as
  ## "is subtype of".
  result = ord(a.kind) - ord(b.kind)
  if result != 0:
    return

  # same kind, compare operands
  case a.kind
  of tkError, tkVoid, tkUnit, tkBool, tkInt, tkFloat:
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

proc errorType*(): SemType {.inline.} =
  SemType(kind: tkError)

proc prim*(kind: TypeKind): SemType {.inline.} =
  ## Returns the primitive type with the given kind.
  SemType(kind: kind)

proc procType*(ret: sink SemType): SemType =
  ## Constructs a procedure type with `ret` as the return type.
  SemType(kind: tkProc, elems: @[ret])

proc `==`*(a, b: SemType): bool =
  ## Compares two types for equality.
  if a.kind != b.kind:
    return false

  case a.kind
  of tkError, tkVoid, tkUnit, tkBool, tkInt, tkFloat:
    result = true
  of tkTuple, tkUnion, tkProc, tkSeq:
    result = a.elems == b.elems

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

proc size*(t: SemType): int =
  ## Computes the size-in-bytes that an instance of `t` occupies in memory.
  case t.kind
  of tkVoid: unreachable()
  of tkError: 8 # TODO: return a value indicating "unknown"
  of tkUnit, tkBool: 1
  of tkInt, tkFloat: 8
  of tkProc: 8 # size of a pointer
  of tkTuple:
    var s = 0
    for it in t.elems.items:
      s += size(it)
    s
  of tkUnion:
    var s = 0
    for it in t.elems.items:
      s = max(s, size(it))
    s + 8 # +8 for the tag
  of tkSeq:
    size(prim(tkInt)) * 2 # length + pointer

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
  of tkError, tkUnit, tkBool, tkInt, tkFloat, tkProc:
    true
  of tkSeq:
    false
  of tkUnion, tkTuple:
    # trivially copyable only if all element types are
    for it in typ.elems.items:
      if not isTriviallyCopyable(it):
        return false
    true
  of tkVoid:
    unreachable()
