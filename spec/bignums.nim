## Provides an arbitrary-precision integers type and the associated arithmetic,
## logical, and comparison operators.

import std/bitops

type Bignum* = object
  ## An arbitrary-precision integer.
  limbs: seq[uint64]
    ## * values are stored in the shortest possible two's complement
    ##   representation
    ## * a leading 0 limb is used to distinguish overflowing positive values
    ##   from negative values
    ## * the value '0' is represented by an empty list, so that
    ##   `default(Bignum)` is a valid big number

const
  Zero* = Bignum()
  Ten   = Bignum(limbs: @[10'u64])

# convenience templates:
template len(n: Bignum): int =
  n.limbs.len
template `[]`(n: Bignum, i: untyped): untyped =
  n.limbs[i]
template `[]=`(n: Bignum, i, val: untyped) =
  n.limbs[i] = val

proc last(n: Bignum): uint64 =
  if n.len == 0: 0'u64
  else:          n[^1]

proc cons(limbs: varargs[uint64]): Bignum {.used.} =
  ## Private helper function for use by unit tests.
  Bignum(limbs: @limbs)

proc adc(a, b: uint64, carry: bool): (uint64, bool) =
  ## Add with carry bit. Returns the result and new carry bit.
  let r1 = a + b
  let r2 = r1 + uint64(ord(carry))
  (r2, r2 < r1 or r1 < a)

proc add(a, b: uint64): (uint64, bool) =
  ## Add `a` and `b` and return the carry bit.
  let r = a + b
  (r, r < a)

proc bignum*(x: SomeInteger): Bignum =
  ## Converts `x` to a big number.
  if x == 0:
    Zero
  else:
    when x is int64:
      Bignum(limbs: @[cast[uint64](x)])
    elif x is SomeSignedInt:
      Bignum(limbs: @[cast[uint64](int64(x))])
    else:
      if x shr 63 == 1:
        Bignum(limbs: @[x, 0])
      else:
        Bignum(limbs: @[x])

proc isNeg*(x: Bignum): bool =
  ## Whether `x` is a negative number.
  x.len > 0 and (x[^1] shr 63) == 1

proc normalize(n: var Bignum, an, bn: bool, carry: bool) =
  ## Normalizes the result of an addition (`n`). `an` and `bn` indicate
  ## whether the operands were negative.
  if carry and an == bn:
    # only pos + pos and neg + neg can meaningfully overflow; the carry bit
    # indicates a change in sign, otherwise
    if an:
      # if the MSB doesn't change, nothing needs to be extended
      if (n.last shr 63) == 0:
        n.limbs.add high(uint64)
    else:
      n.limbs.add 1'u64
  elif n.isNeg:
    if an == bn and not an:
      # positive + positive can only be positive
      n.limbs.add 0'u64
    else:
      # normalize; trim unnecessary ones
      var i = n.len - 1
      while i >= 1 and n[i] == high(uint64) and (n[i - 1] shr 63) == 1:
        dec i
      n.limbs.setLen(i + 1)
  else:
    # normalize; trim unnecessary zeros
    var i = n.len - 1
    while i >= 0 and n[i] == 0 and (i == 0 or (n[i - 1] shr 63) == 0):
      dec i
    n.limbs.setLen(i + 1)

proc trimLastNeg(x: var Bignum) =
  ## Removes the last limb if negative and superfluous.
  if x.len > 1 and x.last == high(uint64) and (x[^2] shr 63) == 1:
    x.limbs.shrink(x.len - 1)

proc fastLog2*(a: Bignum): int =
  ## Computes the integer binary logarithm.
  if a.last == 0:
    if a.len == 0: 0 else: (a.len - 1) * 64 - 1
  else:
    fastLog2(a.limbs[^1]) + (a.limbs.len - 1) * 64

proc `+`*(a: sink Bignum, b: Natural): Bignum =
  if a.len == 0:
    # handle empty numbers
    if b == 0: return a
    else:      return bignum(b)

  result = a
  let wasNegative = result.isNeg
  var overflow = cast[uint64](b)
  var i = 0
  while i < result.len and overflow != 0:
    var carry: bool
    (result[i], carry) = add(result[i], overflow)
    overflow = ord(carry).uint64
    inc i

  normalize(result, wasNegative, false, overflow != 0)

proc `+`*(a, b: Bignum): Bignum =
  ## Arbitrary-precision integer addition.
  if a.len < b.len:
    return b + a
  elif b.len == 0:
    return a

  # `a` is always the number with more limbs
  result.limbs.newSeq(a.len)
  var carry = false
  var i = 0
  # add the common limbs:
  while i < b.len:
    (result[i], carry) = adc(a[i], b[i], carry)
    inc i
  if b.isNeg:
    # treat all missing bits as one
    while i < a.limbs.len:
      (result[i], carry) = adc(a[i], high(uint64), carry)
      inc i
  else:
    # treat all missing bits as zero
    while i < a.limbs.len:
      (result[i], carry) = adc(a[i], 0, carry)
      inc i

  normalize(result, a.isNeg, b.isNeg, carry)

proc `-`*(x: sink Bignum): Bignum =
  ## Yields the two's complement of `x`.
  let last = x.last
  result = x
  var carry = true
  for val in result.limbs.mitems:
    (val, carry) = add(not(val), uint64 ord(carry))

  if (result.last shr 63) == 1 and (last shr 63) == 1:
    # edge case: the two's complement of x is equal to x, but the value is
    # positive now
    result.limbs.add 0'u64
  else:
    # inverting can produce a superfluous last limb
    trimLastNeg(result)

proc `-`*(a, b: Bignum): Bignum =
  ## Arbitrary-precision integer subtraction.
  a + (-b)

proc `shl`*(x: sink Bignum, by: int): Bignum =
  ## Arithmetic left shift. The sign bit is extended.
  if x.len == 0 or by == 0:
    result = x
  elif (by and 63) == 0:
    # shift whole limbs
    result = x
    let by = by shr 6 # div 64
    let L = result.len
    result.limbs.setLen(L + by)
    for i in countdown(L-1, 0):
      result[i + by] = result[i]
    # shift in zeros from the right:
    for i in 0..<by:
      result[i] = 0
    # nothing to normalize, the leading zero already exists when needed
  else:
    let
      wasNegative = x.isNeg
      bias  = by shr 6
      shift = by and 63
    result.limbs.newSeq((fastLog2(x) + 64 + by) shr 6)
    var overflow = 0'u64
    for i, it in x.limbs.pairs:
      result[i + bias] = overflow + (it shl shift)
      overflow = it shr (64 - shift)

    if overflow != 0:
      result.limbs[x.limbs.len + bias] += overflow

    if (result.last shr 63) == 1:
      if not wasNegative:
        # mark as unsigned
        result.limbs.add 0
    elif wasNegative:
      # sign extend the high limb
      result[^1] = cast[uint64](cast[int64](result[^1] shl (64-shift)) shr (64-shift))
      result.trimLastNeg()

proc `shr`*(x: sink Bignum, by: int): Bignum =
  ## Arithmetic right shift.
  if x.len == 0 or by == 0:
    result = x
  elif (by and 63) == 0:
    # shift whole limbs
    result = x
    let
      neg  = result.isNeg
      bias = by shr 6 # div 64
      L = result.len
    for i in 0..<(result.len - bias):
      result[i] = result[i + bias]
    result.limbs.setLen(L - bias)

    if result.len == 0 and neg:
      # make sure `negative shr x` doesn't result in 0
      result.limbs.add high(uint64)
  else:
    let
      neg   = x.isNeg
      shift = by and 63
      bias  = by shr 6
    result.limbs.newSeq((fastLog2(x) + 64 - by) shr 6)
    var overflow = 0'u64
    for i in countdown(x.limbs.high, bias):
      if i - bias < result.len:
        result[i - bias] = overflow + (x[i] shr shift)
      overflow = x[i] shl (64 - shift)

    if (result.last shr 63) == 1:
      if not neg:
        # mark as unsigned
        result.limbs.add 0
    elif neg:
      # sign extend the high limb
      result[^1] = cast[uint64](cast[int64](result[^1] shl shift) shr shift)
      result.trimLastNeg()

proc cmp*(a, b: Bignum): int =
  if a.isNeg and not b.isNeg:
    -1
  elif not(a.isNeg) and b.isNeg:
    1
  elif a.len != b.len:
    if a.isNeg:
      b.len - a.len
    else:
      a.len - b.len
  else:
    # same length
    for i in countdown(a.len - 1, 0):
      if a[i] < b[i]:
        return -1
      elif a[i] > b[i]:
        return 1
    0

proc `<`*(a, b: Bignum): bool =
  ## Less-than comparison.
  cmp(a, b) < 0

proc `<=`*(a, b: Bignum): bool =
  ## Less-than-or-equal comparison.
  cmp(a, b) <= 0

proc addShift(a: var Bignum, b: Bignum, by: int) =
  ## Adds `b` shifted by `by` to `a`. Both numbers must be positive.
  assert not b.isNeg
  let start = by shr 6
  let shift = by and 63

  if a.len < b.len + start:
    a.limbs.setLen(b.len + start)

  var overflow = 0'u64
  var i = 0
  # add the common limbs:
  while i < b.len:
    var carry: bool
    (a[i + start], carry) = add(a[start + i], b[i] shl shift)
    var next = uint64 ord(carry)
    (a[i + start], carry) = add(a[start + i], overflow)
    next += uint64 ord(carry)
    if shift != 0:
      next += b[i] shr (64 - shift)
      # ^^ cannot overflow, because the MSB is never set

    overflow = next
    inc i

  # add the overflow to the remaining limbs:
  while overflow != 0 and i < a.len:
    var carry: bool
    (a[i], carry) = add(a[i], overflow)
    overflow = ord(carry).uint64
    inc i

  if overflow != 0:
    a.limbs.add overflow
  # adding a zero-limb for disambiguation is left to the callsite

proc `*`*(a: Bignum, b: Natural): Bignum =
  if a.len == 0 or b == 0:
    return Zero
  elif a.isNeg:
    return -(-a * b)

  # simple shift-and-add implementation
  let last = fastLog2(b)
  for i in 0..last:
    if (b and (1 shl i)) != 0:
      result.addShift(a, i)

  if (result.last shr 63) == 1:
    result.limbs.add 0'u64

proc `*`*(a, b: Bignum): Bignum =
  ## Arbitrary-precision integer multiplication.
  if a.len == 0 or b.len == 0:
    return Zero
  elif b.isNeg:
    return -(a * (-b))
  elif a.isNeg:
    return -(-a * b)

  # simple shift-and-add implementation
  let last = fastLog2(b)
  for i in 0..last:
    # limb: divide by 64
    # bit:  modulo 64
    if (b[i shr 6] and (1'u64 shl (i and 63))) != 0:
      result.addShift(a, i)

  if (result.last shr 63) == 1:
    result.limbs.add 0'u64

proc udivMod*(dividend, divisor: Bignum): (Bignum, Bignum) =
  ## Arbitrary-precision division where the inputs have to be positive values.
  ## Returns the quotient and remainder.
  if divisor > dividend:
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
    if remainder >= divisor:
      remainder = remainder - divisor
      quotient = quotient + 1

    divisor = divisor shr 1

  result[0] = quotient
  result[1] = remainder

proc divMod*(dividend, divisor: Bignum): (Bignum, Bignum) =
  ## Arbitrary-precision truncating integer division (sign of the remainder
  ## matches that of the dividend).
  let
    ndivisor  = isNeg(divisor)
    ndividend = isNeg(dividend)
    a = if ndividend: -dividend else: dividend
    b = if ndivisor:  -divisor  else: divisor
  result = udivMod(a, b)
  if ndivisor xor ndividend:
    # the quotient must be negative
    result[0] = -result[0]
  if ndividend:
    result[1] = -result[1]

proc `div`*(a, b: Bignum): Bignum =
  ## Arbitrary-precision truncating integer division.
  divMod(a, b)[0]

proc add*(result: var string; value: Bignum) =
  ## Renders `value` to a string and appends it to `result`.
  if value.len == 0:
    result.add "0"
    return

  var value = value
  let neg = isNeg(value)
  if neg:
    value = -value
    result.add "-"

  let start = result.len
  while value != Zero:
    let (q, r) = udivMod(value, Ten)
    result.add "0123456789"[r.last]
    value = q

  # the characters are in the wrong order! reverse them by swapping
  var
    i = start
    j = high(result)
  while i < j:
    swap(result[i], result[j])
    i += 1
    j -= 1

proc `$`*(x: Bignum): string =
  result.add(x)

proc parseBignum*(x: string): Bignum =
  ## Parses a big number from `x`.
  var i = 0
  if x[0] == '-':
    inc i

  while i < x.len and x[i] in {'0'..'9'}:
    result = result * 10
    result = result + (ord(x[i]) - ord('0'))
    inc i

  if x[0] == '-':
    result = -result

proc `'n`*(s: string): Bignum {.compiletime.} =
  parseBignum(s)

proc toInt*(n: Bignum): int64 =
  ## Converts `n` to a 64-bit signed integer. `n` must be in range.
  assert n.len <= 1
  cast[int64](n.last)

# some additional operators (also also present for normal integers) that build
# upon the basic operators:

proc succ*(x: sink Bignum): Bignum {.inline.} = x + 1
proc pred*(x: sink Bignum): Bignum {.inline.} = x + -1'n

proc `inc`*(a: var Bignum; b = 1) =
  ## Increments `a` by `b`.
  if b >= 0:
    a = a + b
  else:
    a = a + bignum(b)

proc abs*(x: sink Bignum): Bignum =
  ## Returns the absolute value of `x`.
  if x.isNeg: -x
  else:       x

template `..<`*(a, b: Bignum): Slice[Bignum] =
  ## Constructs a half-open slice from `a` and `b`.
  a .. pred(b)
