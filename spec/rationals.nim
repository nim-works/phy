## Provides a simple implementation for rational numbers and operations
## on them.

import
  bignums,
  std/math

type Rational* = object
  ## A rational number represented as a fraction of two arbitrary-precision
  ## integers.
  num, den: Bignum

const
  One = 1'n

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
  ## Parses a rational number from `s`. `s` must use either the "i.i" or "i/i"
  ## rational number representation.
  var i = 0
  if s[0] == '-':
    inc i
  var num = Zero
  while i < s.len and s[i] in '0'..'9':
    num = num * 10
    num = num + (ord(s[i]) - ord('0'))
    inc i

  var denom = One
  if i < s.len and s[i] == '.':
    inc i
    while i < s.len and s[i] in '0'..'9':
      num = num * 10
      num = num + (ord(s[i]) - ord('0'))
      denom = denom * 10
      inc i
  elif i < s.len and s[i] == '/':
    inc i
    denom = Zero
    while i < s.len and s[i] in '0'..'9':
      denom = denom * 10
      denom = denom + (ord(s[i]) - ord('0'))
      inc i

  if s[0] == '-':
    num = -num

  result = frac(num, denom)

proc addRat*(res: var string, r: Rational) =
  ## Adds the text representation of `r` to `res`, which is either a fraction
  ## (i.e, "x/y") or a decimal number.
  if r.den == One:
    # it's an integer number
    res.add(r.num)
  else:
    let start = res.len
    let (i, frac) = split(r)
    if i == Zero and frac.num.isNeg:
      # it's a negative number greater than -1
      res.add '-'
    res.add(i)
    res.add '.'
    var num = frac.num * 10
    if num.isNeg:
      num = -num
    # multiply by ten and divide by the denominator until there's
    # no remainder left
    var step = 0
    while num != Zero and step < 10: # 10 digits at max
      let (quot, rem) = udivMod(num, frac.den)
      res.add quot
      num = rem * 10
      inc step

    if num != Zero and step == 10:
      # fall back to rendering as a fraction
      res.setLen(start)
      res.add(r.num)
      res.add '/'
      res.add(r.den)

proc `$`*(r: Rational): string =
  result.addRat(r)

proc rational*(f: float): Rational =
  ## Converts `f` to a rational number. All finite float values can are are
  ## represented *exactly*. Zero (both signed and unsigned) are converted to
  ## 0 and inf and nan are forbidden.
  proc convert(m: uint64, exp: int, sign: bool): Rational =
    if exp < 0:
      result = frac(bignum(m), 1'n shl (-exp))
    else:
      # it's an integer number
      result = frac(bignum(m) shl exp, 1'n)

    if sign:
      result = -result

  case classify(f)
  of fcNormal:
    let bits = cast[uint64](f)
    let m = (bits and 0xF_FFFF_FFFF_FFFF'u64) or (1 shl 52)
    convert(m, int((bits shr 52) and 0x7FF) - 1075, f < 0)
  of fcSubnormal:
    let bits = cast[uint64](f)
    convert(bits and 0xF_FFFF_FFFF_FFFF'u64, -1074, f < 0)
  of fcZero, fcNegZero:
    rational(0)
  of fcInf, fcNegInf, fcNan:
    assert false, "not a rational value"
    rational(0)
