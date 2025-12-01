## Implements the storage for literal data embedded in ASTs.

# TODO: use bi-tables for the number and string values
# TODO: store small integers inline (like how the packing in `trees` does it)

type
  Literals* = object
    ## Storage container for literal data, to be used with nanopass ASTs.
    numbers*: seq[uint64] ## a list of bit patterns
    strings*: seq[string]

  Ident* = distinct string

proc pack*(s: var Literals, val: SomeInteger): uint32 {.inline.} =
  ## Adds the bit-representation of `val` to `s` and returns an ID to refer
  ## to the value with later.
  result = uint32(s.numbers.len)
  s.numbers.add cast[uint64](val)

proc pack*(s: var Literals, val: float): uint32 {.inline.} =
  ## Adds the bit-representation of `val` to `s` and returns an ID to refer
  ## to the value with later.
  result = uint32(s.numbers.len)
  s.numbers.add cast[uint64](val)

proc pack*(s: var Literals, val: string): uint32 {.inline.} =
  ## Adds the `val` to `s` and returns an ID to refer to the value with later.
  result = uint32(s.strings.len)
  s.strings.add val

proc pack*(s: var Literals, val: Ident): uint32 {.inline.} =
  ## Adds the `val` to `s` and returns an ID to refer to the value with later.
  result = uint32(s.strings.len)
  s.strings.add string(val)

proc unpack*[T: SomeNumber](s: Literals, id: uint32, _: typedesc[T]): T {.inline.} =
  ## Returns the bit-representation stored under `id` interpreted as `T`.
  when T is uint64: # prevent warnings
    s.numbers[id]
  else:
    cast[T](s.numbers[id])

proc unpack*(s: Literals, id: uint32, _: typedesc[string]): lent string {.inline.} =
  ## Returns the string stored under `id`.
  s.strings[id]

proc unpack*(s: Literals, id: uint32, _: typedesc[Ident]): lent Ident {.inline.} =
  ## Returns the string stored under `id`, treated as an ``Ident``.
  s.strings[id].Ident

# TODO: remove the temporary overloads for objects again

proc pack*[T: object](s: Literals, val: T): uint32 =
  result = 0

proc unpack*[T: object](s: Literals, id: uint32, _: typedesc[T]): T =
  discard
