discard """
  description: "Tests for rational numbers"
"""

import spec/[bignums, rationals]

proc frac(a, b: int): Rational = frac(bignum(a), bignum(b))

block equality:
  # make sure non-normal-form fractions are equal to their corresponding
  # normal form
  doAssert frac(2, 4) == frac(1, 2) # non-integer number
  doAssert frac(4, 2) == frac(2, 1) # integer; directly dividable
  doAssert frac(10, 4) == frac(5, 2) # not directly dividable
  # sign correctness
  doAssert frac(-1, 4) == frac(1, -4) # non-integer number
  doAssert frac(-4, 1) == frac(4, -1) # integer number
  doAssert frac(-10, 4) == frac(10, -4) # not directly dividable
  doAssert frac(-1, 4) != frac(1, 4)

block addition:
  # make sure addition works
  doAssert frac(2, 1) + frac(0, 1) == frac(2, 1) # with identity value
  doAssert frac(2, 1) + frac(2, 1) == frac(4, 1) # natural numbers
  doAssert frac(1, 2) + frac(1, 2) == frac(1, 1) # same denominator
  doAssert frac(1, 3) + frac(1, 3) == frac(2, 3)
  doAssert frac(1, 3) + frac(1, 4) == frac(7, 12) # different denominator
  doAssert frac(-2, 1) + frac(4, 1) == frac(2, 1)

block subtraction:
  # make sure subtraction works
  doAssert frac(2, 1) - frac(0, 1) == frac(2, 1) # with identity value
  doAssert frac(2, 1) - frac(2, 1) == frac(0, 1)
  doAssert frac(2, 2) - frac(1, 2) == frac(1, 2)
  doAssert frac(2, 3) - frac(1, 3) == frac(1, 3)
  doAssert frac(1, 3) - frac(1, 4) == frac(1, 12)
  doAssert frac(2, 1) - frac(4, 1) == frac(-2, 1)

block multiplication:
  doAssert frac(5, 1) * frac(0, 1) == frac(0, 1)
  doAssert frac(1, 1) * frac(1, 1) == frac(1, 1) # with identity value
  doAssert frac(2, 1) * frac(4, 1) == frac(8, 1) # natural numbers
  doAssert frac(1, 2) * frac(1, 4) == frac(1, 8) # non-integer numbers
  doAssert frac(1, 3) * frac(6, 1) == frac(2, 1)
  # sign correctness
  doAssert frac(-1, 4) * frac(2, 4) == frac(-1, 8)
  doAssert frac(-1, 4) * frac(-2, 4) == frac(1, 8)

block division:
  doAssert frac(1, 1) / frac(1, 1) == frac(1, 1) # with identity value
  doAssert frac(6, 1) / frac(3, 1) == frac(2, 1) # natural numbers
  doAssert frac(3, 1) / frac(6, 1) == frac(1, 2)
  doAssert frac(4, 1) / frac(1, 2) == frac(8, 1)
  doAssert frac(1, 2) / frac(4, 1) == frac(1, 8)
  doAssert frac(1, 2) / frac(1, 4) == frac(2, 1) # non-integer numbers
  # sign correctness
  doAssert frac(-1, 4) / frac(2, 4) == frac(-1, 2)
  doAssert frac(-1, 4) / frac(-2, 4) == frac(1, 2)

block comparison:
  # test natural numbers:
  for i in 0..<100:
    for j in 0..<100:
      doAssert (frac(i, 1) < frac(j, 1)) == (i < j)
      doAssert (frac(i, 1) <= frac(j, 1)) == (i <= j)

  # test non-natural numbers
  doAssert frac(2, 5) < frac(1, 2)
  doAssert frac(1, 2) > frac(1, 4)
  doAssert frac(1, 1) > frac(1, 4)
  doAssert frac(4, 1) > frac(8, 9)

block split:
  doAssert split(frac(2, 1))  == (bignum(2), frac(0, 1))
  doAssert split(frac(-2, 1)) == (bignum(-2), frac(0, 1))
  doAssert split(frac(1, 4))  == (bignum(0), frac(1, 4))
  doAssert split(frac(5, 4))  == (bignum(1), frac(1, 4))
  doAssert split(frac(-1, 4)) == (bignum(0), frac(-1, 4))
  doAssert split(frac(-5, 4)) == (bignum(-1), frac(-1, 4))

block parsing:
  doAssert parseRational("0.5") == frac(1, 2)
  doAssert parseRational("0.3") == frac(3, 10)
  doAssert parseRational("1.5") == frac(3, 2)
  doAssert parseRational("-0.5") == frac(-1, 2)
  doAssert parseRational("-0.3") == frac(-3, 10)
  doAssert parseRational("-1.5") == frac(-3, 2)

block stringify:
  doAssert $frac(1, 2) == "0.5"
  doAssert $frac(1, 3) == "0.333333333333333333333333333333"
  doAssert $frac(1, 4) == "0.25"
  doAssert $frac(1, 5) == "0.2"
  doAssert $frac(11, 5) == "2.2"
  doAssert $frac(-1, 2) == "-0.5"
  doAssert $frac(-3, 2) == "-1.5"
