## Provides an implementation of 128-bit wide integers and their arithmetic
## operations.

import std/bitops

type Int128* = object
  ## A signless 128-bit integer.
  lo, hi: uint64

const
  Zero* = Int128()

proc toInt128*(x: SomeInteger): Int128 =
  result.lo = cast[uint64](x)
  if x is SomeSignedInt and x < 0:
    result.hi = high(uint64) # sign extend the lower bits

proc toInt*(x: Int128): int =
  ## Cuts off the most-significant 64 bits.
  cast[int](x.lo)

proc fastLog2*(a: Int128): int =
  if a.hi != 0:
    64 + fastLog2(a.hi)
  else:
    fastLog2(a.lo)

proc isNeg*(x: Int128): bool = x.hi > uint64(high(int64))

proc `+`*(a, b: Int128): Int128 =
  result.lo = a.lo + b.lo
  # add-with-carry
  result.hi = a.hi + b.hi + ord(result.lo < a.lo).uint64

proc `-`*(a, b: Int128): Int128 =
  result.lo = a.lo - b.lo
  result.hi = a.hi - b.hi - ord(result.lo > a.lo).uint64

proc `-`*(x: Int128): Int128 =
  ## Yields the two's complement of `x`.
  result.lo = not(x.lo)
  result.hi = not(x.hi)
  result = result + Int128(lo: 1)

proc `shl`*(x: Int128, by: int): Int128 =
  ## Logical left shift.
  let by = by and 127
  if by == 0:
    result = x
  elif by < 64:
    result.lo = (x.lo shl by)
    result.hi = (x.hi shl by) or (x.lo shr (64 - by))
  else:
    result.lo = 0
    result.hi = x.lo shl (64 - (128 - by))

proc `shr`*(x: Int128, by: int): Int128 =
  ## Logical right shift.
  let by = by and 127
  if by == 0:
    result = x
  elif by < 64:
    result.lo = (x.lo shr by) or (x.hi shl (64 - by))
    result.hi = (x.hi shr by)
  else:
    result.lo = (x.hi shr (by - 64))
    result.hi = 0

proc `<%`*(a, b: Int128): bool =
  ## Unsigned less-than comparison.
  if a.hi < b.hi: true
  elif a.hi == b.hi: a.lo < b.lo
  else: false

proc `<=%`*(a, b: Int128): bool =
  ## Unsigned less-than-or-equal comparison.
  if a.hi < b.hi: true
  elif a.hi == b.hi: a.lo <= b.lo
  else: false

proc `<`*(a, b: Int128): bool =
  ## Signed less-than comparison.
  if cast[int64](a.hi) < cast[int64](b.hi): true
  elif a.hi == b.hi: a.lo < b.lo
  else: false

proc `<=`*(a, b: Int128): bool =
  ## Signed less-than-or-equal comparison.
  if cast[int64](a.hi) < cast[int64](b.hi): true
  elif a.hi == b.hi: a.lo <= b.lo
  else: false

proc `*`*(a, b: Int128): Int128 =
  ## 128-bit integer multiplication.
  # a * b = (aLo + aHi*shift) * (bLo + bHi*shift)
  #       = aLo*bLo + aLo*bHi*shift + aHi*bLo*shift + aHi*bHi*shift*shift
  #       = aLo*bLo + (aLo*bHi)<<64 + (aHi*bLo)<<64 + (aHi*bHi)<<128
  # splitting the multiplication like this makes it possible to calculate
  # the result using only 64-bit arithmetic. `aLo*bLo` needs to be subdivided
  # further, as the overflow of the multiplication needs to carry over into the
  # high bits (for the other subterms, the overflow can only be discarded).
  let
    a32 = a.lo shr 32
    a00 = a.lo and 0xFFFF_FFFF'u64
    b32 = b.lo shr 32
    b00 = b.lo and 0xFFFF_FFFF'u64

  result = Int128(hi: a32 * b32 + a.hi * b.lo + a.lo * b.hi, lo: a00 * b00)
  result = result + (Int128(lo: a32 * b00) shl 32)
  result = result + (Int128(lo: a00 * b32) shl 32)

proc udivMod*(dividend, divisor: Int128): (Int128, Int128) =
  ## Unsigned 128-integer division. Returns the quotient and
  ## remainder.
  if divisor >% dividend:
    return (Zero, dividend)

  # shift-subtract algorithm (refer to
  # https://blog.segger.com/algorithms-for-division-part-2-classics)
  var
    quotient = Zero
    remainder = dividend

  let digits = fastLog2(dividend) - fastLog2(divisor)
  var divisor = divisor shl digits

  for _ in 0..digits:
    quotient = quotient shl 1
    if remainder >=% divisor:
      remainder = remainder - divisor
      quotient.lo = quotient.lo or 1 # left-shift 1 into the quotient

    divisor = divisor shr 1

  result[0] = quotient
  result[1] = remainder

proc divMod*(dividend, divisor: Int128): (Int128, Int128) =
  ## Signed 128-bit truncating integer division (sign of the remainder matches
  ## that of the dividend).
  let
    ndivisor = isNeg(divisor)
    ndividend = isNeg(dividend)
    a = if ndividend: -dividend else: dividend
    b = if ndivisor:  -divisor  else: divisor
  result = udivMod(a, b)
  if ndivisor xor ndividend:
    # if either the divisor or dividend is negative (but not both), the
    # quotient is too
    result[0] = -result[0]
  if ndividend:
    result[1] = -result[1]

proc `div`*(a, b: Int128): Int128 =
  ## Signed 128-bit truncating integer division.
  divMod(a, b)[0]

proc addInt128*(result: var string; value: Int128) =
  ## Renders the signed `value` to a string and appends it to `result`.
  if value.lo == value.hi and value.lo == 0:
    result.add "0"
    return

  var value = value
  let neg = isNeg(value)
  if neg:
    value = -value # compute the absolute
    result.add "-"

  let start = result.len
  while value != Zero:
    let (q, r) = udivMod(value, Int128(lo: 10))
    result.add "0123456789"[r.lo]
    value = q

  # the characters are in the wrong order! reverse them by swapping
  var
    i = start
    j = high(result)
  while i < j:
    swap(result[i], result[j])
    i += 1
    j -= 1

proc `$`*(x: Int128): string =
  result.addInt128(x)

proc parseInt128*(x: string): Int128 =
  ## Parses a 128-bit signed or unsigned integer from `x`.
  var i = 0
  if x[0] == '-':
    inc i

  while i < x.len and x[i] in {'0'..'9'}:
    result = result * Int128(lo: 10)
    result = result + Int128(lo: uint64(ord(x[i]) - ord('0')))
    inc i

  if x[0] == '-':
    result = -result
