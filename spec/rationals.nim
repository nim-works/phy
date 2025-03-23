## Provides a simple implementation for rational numbers and operations
## on them.

import bignums

type Rational* = object
  ## A rational number represented as a fraction of two arbitrary-precision
  ## integers.
  num, den: Bignum

const
  One = 1'n
  Ten = 10'n

proc reduced(r: sink Rational): Rational =
  ## Returns the normal form for `r`. The normal form uses the smallest
  ## possible positive denominator.
  if r.num == Zero:
    Rational(num: Zero, den: One)
  else:
    # compute the greatest denominator common between `r.num` and `r.denom`.
    # Use unsigned values because it doesn't affect the result and unsigned
    # division is faster
    var
      num = abs(r.num)
      denom = abs(r.den)
    while num != Zero:
      let (_, rem) = udivMod(denom, num)
      denom = num
      num = rem

    if r.den.isNeg:
      # invert the result, so that the denominator is positive
      Rational(num: -(r.num div denom), den: -(r.den div denom))
    else:
      Rational(num: r.num div denom, den: r.den div denom)

proc frac*(num, denom: Bignum): Rational =
  ## Creates a fraction from `num` and `denom`.
  assert denom != Zero
  reduced(Rational(num: num, den: denom))

proc `+`*(a, b: Rational): Rational =
  if a.den == b.den:
    reduced(Rational(num: a.num + b.num, den: a.den))
  else:
    reduced(Rational(num: a.num * b.den + b.num * a.den, den: a.den * b.den))

proc `-`*(a, b: Rational): Rational =
  if a.den == b.den:
    reduced(Rational(num: a.num - b.num, den: a.den))
  else:
    reduced(Rational(num: a.num * b.den - b.num * a.den, den: a.den * b.den))

proc `-`*(a: sink Rational): Rational =
  Rational(num: -a.num, den: a.den)
proc `*`*(a, b: Rational): Rational =
  reduced(Rational(num: a.num * b.num, den: a.den * b.den))
proc `/`*(a, b: Rational): Rational =
  reduced(Rational(num: a.num * b.den, den: a.den * b.num))
proc `<`*(a, b: Rational): bool =
  a.num * b.den < b.num * a.den
proc `<=`*(a, b: Rational): bool =
  a.num * b.den <= b.num * a.den

proc reciprocal*(x: sink Rational): Rational =
  ## Computes and returns the reciprocal of `x` (that is, `1 / x`).
  if x.num.isNeg:
    # keep the denominator positive
    Rational(num: -x.den, den: -x.num)
  else:
    Rational(num: x.den, den: x.num)

proc split*(r: Rational): tuple[i: Bignum, frac: Rational] =
  ## Splits `r` into the integer and fractional parts, such that
  ## ``int + frac = r``.
  result.i = r.num div r.den
  result.frac = reduced(Rational(num: r.num - (result.i * r.den), den: r.den))

proc isInt*(r: Rational): bool =
  ## Whether `r` is an integer number.
  r.den == One

proc rational*(i: SomeInteger): Rational {.inline.} =
  ## Lossless conversion from ``int`` to ``Rational``.
  Rational(num: bignum(i), den: One)

proc rational*(i: Bignum): Rational {.inline.} =
  ## Lossless conversion from ``Bignum`` to ``Rational``.
  Rational(num: i, den: One)

proc toInt*(r: Rational): Bignum =
  ## Converts `r`, which must be a valid integer number, to an int.
  assert r.den == One
  r.num

proc parseRational*(s: string): Rational =
  ## Parses a rational number from `s`. `s` must be a well-formed rational
  ## number representation.
  var i = 0
  if s[0] == '-':
    inc i
  var num = Zero
  while i < s.len and s[i] != '.':
    num = num * Ten
    num = num + (ord(s[i]) - ord('0'))
    inc i

  var denom = One
  if i < s.len and s[i] == '.':
    inc i
    while i < s.len:
      num = num * Ten
      num = num + (ord(s[i]) - ord('0'))
      denom = denom * Ten
      inc i

  if s[0] == '-':
    num = -num

  result = reduced(Rational(num: num, den: denom))

proc addRat*(res: var string, r: Rational) =
  ## Adds the text representation of `r` to `res`.
  if r.den == One:
    # it's an integer number
    res.add(r.num)
  else:
    let (i, frac) = split(r)
    if i == Zero and frac.num.isNeg:
      # it's a negative number greater than -1
      res.add '-'
    res.add(i)
    res.add '.'
    var num = frac.num * Ten
    if num.isNeg:
      num = -num
    # multiply by ten and divide by the denominator until there's
    # no remainder left
    var step = 0
    while num != Zero and step < 30: # 30 digits at max
      let (quot, rem) = udivMod(num, frac.den)
      res.add quot
      num = rem * Ten
      inc step

proc `$`*(r: Rational): string =
  result.addRat(r)
