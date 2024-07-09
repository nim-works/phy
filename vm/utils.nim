## Contains various not-yet sorted routines. These should eventually move into
## elswhere.

import std/private/miscdollars

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

# ------- unreachable

type IInfo = typeof(instantiationInfo())

func unreachableImpl(loc: IInfo) {.noinline, noreturn.} =
  var msg: string
  msg.toLocation(loc.filename, loc.line, loc.column + 1)
  msg.add" unreachable"
  raiseAssert(msg)

template unreachable*() =
  ## Use ``unreachable`` to mark a point in the program as unreachable. This
  ## is preferred over ``assert false``.
  unreachableImpl(instantiationInfo(-1))
