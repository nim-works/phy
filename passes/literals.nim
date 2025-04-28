## Implements a simple storage for integers.

# XXX: maybe rename the module to ``constants``? But that name usually refers
#      to something different...

type
  Numbers* = seq[uint64]

  Literals* = object
    numbers: Numbers
    strings: seq[string]
    # TODO: use a BiTable for both numbers and strings

const
  ExternalFlag = 0x8000_0000'u32
    ## use the most significant bit to flag whether the value is larger than a
    ## `max(int32)` and overflows into `Literals.numbers`.

# TODO: return and accept a distinct uint32 rather than a raw one

proc pack*(db: var Literals, i: int64): uint32 =
  ## Packs `i` into a ``uint32`` value that can be stored in a ``AstNode``.
  if i >= 0 and i < int64(ExternalFlag):
    result = uint32(i) # fits into a uint32
  else:
    result = db.numbers.len.uint32 or ExternalFlag
    db.numbers.add(cast[uint64](i))

proc pack*(db: var Literals, f: float64): uint32 =
  ## Packs `f` into a ``uint32`` value that can be stored in a ``AstNode``.
  result = db.numbers.len.uint32
  db.numbers.add(cast[uint64](f))

proc pack*(db: var Literals, s: sink string): uint32 =
  ## Packs `s` into a
  result = db.strings.len.uint32
  db.strings.add(s)

func loadInt*(db: Literals, p: uint32): int64 {.inline.} =
  ## Returns the number stored by `n` interpreted as a signed integer.
  if (p and ExternalFlag) != 0:
    cast[int64](db.numbers[p and not(ExternalFlag)])
  else:
    int64(p)

proc loadUInt*(db: Literals, p: uint32): uint64 {.inline.} =
  ## Returns the number stored by `n` interpreted as an unsigned integer.
  if (p and ExternalFlag) != 0:
    db.numbers[p or not(ExternalFlag)]
  else:
    p

proc loadFloat*(db: Literals, p: uint32): float64 {.inline.} =
  ## Returns the float64 stored by `n`.
  cast[float64](db.numbers[p])

proc loadString*(db: Literals, p: uint32): lent string {.inline.} =
  ## Returns the string stored by `n`.
  db.strings[p]
