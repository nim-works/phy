## Contains various not-yet sorted routines. These should eventually move into
## elswhere.

# ------- HOslice

type HOslice*[T: Ordinal] = object
  ## Half-open slice. Inclusive start, exclusive end.
  a*, b*: T

func hoSlice*[T](a, b: T): HOslice[T] =
  ## Slice constructor.
  HOslice[T](a: a, b: b)

func len*(s: HOslice): int =
  ## The number of values the slice covers.
  int(s.b - s.a)

iterator items*[T](s: HOslice[T]): T =
  ## Returns all values part of the slice.
  for it in s.a..<s.b:
    yield it

# ------- checked arithmetic

proc checkedAdd*[T: SomeUnsignedInt](a, b: T, o: var T): bool =
  o = a + b
  # if adding two non-negative numbers, and the result is smaller than
  # both operands, the operation overflowed
  o < a and o < b

proc checkedAdd*[T: SomeSignedInt](a, b: T, o: var T): bool =
  o = a +% b
  (o xor a) < T(0) and (o xor b) < T(0)
