## Implements the storage for literal data embedded in ASTs.

import nanopass/asts

# TODO: use bi-tables for the number, string, and source location values

type
  Literals* = object
    ## Storage container for literal data, to be used with nanopass ASTs.
    numbers*: seq[uint64] ## a list of bit patterns
    strings*: seq[string]
    locs*: seq[SourceLoc]

const
  OverflowShift = 31
  OverflowBit   = 1'u32 shl OverflowShift
    ## use the most significant bit to flag whether a value is larger than
    ## `max(int32)` and overflows into `PackedTree.numbers`

template castAny[T, U](x: U): T =
  ## A `cast` that doesn't warn when casting into the origin type.
  when T is U: x
  else:        cast[T](x)

proc pack*(s: var Literals, val: SomeInteger): uint32 {.inline.} =
  ## Adds the bit-representation of `val` to `s` and returns an ID to refer
  ## to the value with later.
  when sizeof(val) < 4:
    # always fits into the packed representation
    result = cast[uint32](val)
  else:
    if (val shr OverflowShift) != 0:
      # overflows the packed value range
      result = uint32(s.numbers.len) or OverflowBit
      when val is SomeSignedInt:
        s.numbers.add castAny[uint64](int64(val)) # sign extend
      else:
        s.numbers.add castAny[uint64](val)
    else:
      result = castAny[uint32](val) # fits the packed range

proc pack*(s: var Literals, val: float): uint32 {.inline.} =
  ## Adds the bit-representation of `val` to `s` and returns an ID to refer
  ## to the value with later.
  result = uint32(s.numbers.len)
  s.numbers.add cast[uint64](val)

proc pack*(s: var Literals, val: string): uint32 {.inline.} =
  ## Adds the `val` to `s` and returns an ID to refer to the value with later.
  result = uint32(s.strings.len)
  s.strings.add val

proc unpack*[T: SomeNumber](s: Literals, id: uint32, _: typedesc[T]): T {.inline.} =
  ## Returns the bit-representation stored under `id` interpreted as `T`.
  if (id and OverflowBit) != 0:
    castAny[T](s.numbers[id and not OverflowBit])
  else:
    castAny[T](id)

proc unpack*(s: Literals, id: uint32, _: typedesc[string]): lent string {.inline.} =
  ## Returns the string stored under `id`.
  s.strings[id]

proc pack*(s: var Literals, val: SourceLoc): uint32 {.inline.} =
  ## Adds `val` to the database and returns the ID to later look up `val` with.
  result = uint32(s.locs.len)
  s.locs.add val

proc unpack*(s: Literals, id: uint32, _: typedesc[SourceLoc]
            ): SourceLoc {.inline.} =
  ## Returns the source location earlier stored under `id`.
  s.locs[id]
