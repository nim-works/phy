## Provides a simple implementation for rational numbers and operations
## on them.

import int128

type Rational* = object
  ## A rational number represented as a fraction of two 128-bit integers.
  num, den: Int128

const
  One = toInt128(1)
  Ten = toInt128(10)

proc reduced(r: Rational): Rational =
  ## Returns the smallest possible representation of `r`.
  if r.num == Zero:
    Rational(num: Zero, den: One)
  else:
    # compute the greatest common denominator between `r.num` and `r.denom`:
    var
      num = r.num
      denom = r.den
    while num != Zero:
      let rem = divMod(denom, num)[1]
      denom = num
      num = rem

    if denom.isNeg:
      denom = -denom
    Rational(num: r.num / denom, den: r.den / denom)

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

proc `-`*(a: Rational): Rational =
  Rational(num: -a.num, den: a.den)
proc `*`*(a, b: Rational): Rational =
  reduced(Rational(num: a.num * b.num, den: a.den * b.den))
proc `/`*(a, b: Rational): Rational =
  reduced(Rational(num: a.num * b.den, den: a.den * b.num))
proc `<`*(a, b: Rational): bool =
  a.num * b.den < b.num * a.den
proc `<=`*(a, b: Rational): bool =
  a.num * b.den <= b.num * a.den

proc split*(r: Rational): tuple[i: Int128, frac: Rational] =
  ## Splits `r` into the integer and fractional parts, such that
  ## ``int + frac = r``.
  result.i = r.num / r.den
  result.frac = reduced(Rational(num: r.num - (result.i * r.den), den: r.den))

proc parseRational*(s: string): Rational =
  ## Parses a rational number from `s`. `s` must be a well-formed rational
  ## number representation.
  var i = 0
  if s[0] == '-':
    inc i
  var num = Zero
  while i < s.len and s[i] != '.':
    num = num * Ten
    num = num + toInt128(ord(s[i]) - ord('0'))
    inc i

  var denom = One
  if i < s.len and s[i] == '.':
    inc i
    while i < s.len:
      num = num * Ten
      num = num + toInt128(ord(s[i]) - ord('0'))
      denom = denom * Ten
      inc i

  if s[0] == '-':
    num = -num

  result = reduced(Rational(num: num, den: denom))

proc addRat*(res: var string, r: Rational) =
  ## Adds the text representation of `r` to `res`.
  if r.den == One:
    # it's an integer number
    res.addInt128(r.num)
  else:
    let (i, frac) = split(r)
    if i == Zero and frac.num.isNeg:
      # it's a negative number greater than -1
      res.add '-'
    res.addInt128(i)
    res.add '.'
    var num = frac.num * Ten
    if num.isNeg:
      num = -num
    # multiply by ten and divide by the denominator until there's
    # no remainder left
    var step = 0
    while num != Zero and step < 30: # 30 digits at max
      let (quot, rem) = udivMod(num, frac.den)
      res.addInt toInt(quot)
      num = rem * Ten
      inc step

proc `$`*(r: Rational): string =
  result.addRat(r)
