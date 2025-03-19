discard """
  description: "Tests for the 128-bit integer implementation"
"""

import spec/bignums {.all.}

const Full = high(uint64) # all 64 bits are set

# don't use 'n for early tests, as it relies on parsing, which itself relies
# on working addition and multiplication
proc bn(x: SomeInteger): Bignum =
  bignum(x)

block add_with_carry:
  # test the internal add-with-carry implementation
  doAssert adc(1, 1, false) == (2'u64, false)
  doAssert adc(Full, 1, false) == (0'u64, true)
  doAssert adc(Full, 0, true) == (0'u64, true)
  doAssert adc(Full, 1, true) == (1'u64, true)
  doAssert adc(Full, Full, false) == (Full shl 1, true)
  doAssert adc(Full, Full, true)  == (Full, true)

block negation:
  doAssert -bn(0) == bn(0)
  doAssert -bn(1) == bn(-1)
  doAssert -bn(-1) == bn(1)
  # negation creating an number overflowing the int64 range:
  doAssert -bn(-9223372036854775808) == bn(9223372036854775808'u64)
  # negation requiring limb normalization:
  doAssert -bn(9223372036854775808'u64) == bn(-9223372036854775808)

block basic_addition:
  doAssert bn(0) + bn(0) == bn(0)
  doAssert bn(10) + bn(10) == bn(20)
  doAssert bn(-1) + bn(2) == bn(1) # negative + positive overflows to positive
  doAssert bn(-1) + bn(1) == bn(0) # negative + positive overflows to zero
  doAssert bn(1) + bn(-1) == bn(0) # positive + negative overflows to zero
  doAssert bn(1) + bn(-2) == bn(-1) # positive + negative overflows to negative
  doAssert bn(-1) + bn(-1) == bn(-2)
  # edge case: result overflows 64-bit signed integer range without
  # overflowing the 64-bit unsigned range
  doAssert bn(9223372036854775807) + bn(1) == bn(9223372036854775808'u64)
  # negative + negative overflows the limb:
  doAssert bn(-9223372036854775808) + bn(-1) == -bn(9223372036854775809'u64)
  # multi-limb addition that zeroes out:
  doAssert -bn(9223372036854775809'u64) + bn(9223372036854775809'u64) == bn(0)
  # larger + smaller with no carry:
  doAssert cons(0, 1) + cons(1) == cons(1, 1)
  doAssert cons(1) + cons(0, 1) == cons(1, 1)
  # larger + smaller with carry:
  doAssert cons(0b11'u64 shl 62, 0x1) + bn(1'u64 shl 62) == cons(0, 0b10)
  doAssert bn(1'u64 shl 62) + cons(0b11'u64 shl 62, 1) == cons(0, 0b10)
  # larger negative + smaller positive:
  doAssert -bn(9223372036854775809'u64) + bn(1) == bn(-9223372036854775808)
  doAssert bn(1) + -bn(9223372036854775809'u64) == bn(-9223372036854775808)
  # larger positive + smaller negative:
  doAssert bn(9223372036854775808'u64) + bn(-1) == bn(9223372036854775807)
  doAssert bn(-1) + bn(9223372036854775808'u64) == bn(9223372036854775807)
  # integration test for internal `adc` (add with carry):
  const Large = cons(Full, Full, 0)
  doAssert Large + Large == cons(Full shl 1, Full, 1)

block basic_left_shift:
  doAssert bn(0) shl 1 == bn(0)
  doAssert bn(2) shl 0 == bn(2)
  doAssert bn(2) shl 1 == bn(4)
  # shift by power-of-64:
  doAssert bn(1) shl 64 == cons(0, 1)
  doAssert bn(1) shl 128 == cons(0, 0, 1)
  # shift negative number:
  doAssert bn(-1) shl 1 == bn(-2)
  # shift negative number across limbs:
  doAssert bn(-1) shl 65 == cons(0, cast[uint64](-2))
  # shift by less than one limb, adding one new limb:
  doAssert bn(0b1010) shl 62 == cons(9223372036854775808'u64, 0b10)
  # shift by less than two limbs, adding two new limbs:
  doAssert bn(0b1010) shl 126 == cons(0x0, 9223372036854775808'u64, 0b10)
  # shift one into the MSL's MSB:
  doAssert bn(1) shl 63 == bn(9223372036854775808'u64)
  doAssert bn(1) shl 127 == cons(0, 9223372036854775808'u64, 0)

block basic_right_shift:
  doAssert bn(1) shr 0 == bn(1) # shift by zero
  doAssert bn(0) shr 1 == bn(0) # shift zero
  doAssert bn(-1) shr 1 == bn(-1)
  doAssert bn(-6) shr 1 == bn(-3)
  # shift a negative number by a full limb:
  doAssert bn(-1) shr 64 == bn(-1)
  # shift by less than two limbs, removing two limbs:
  doAssert cons(0x0, (1'u64 shl 63), 0b10) shr 67 == bn(0b0101 shl 60)
  # shift 1 into the MSL's MSB (negative input):
  doAssert (bn(-1) shl 64)  shr  1 == bn(-9223372036854775808)
  doAssert (bn(-1) shl 128) shr 65 == bn(-9223372036854775808)
  # shift 1 into the MSL's MSB (positive input):
  doAssert cons(0, 1)    shr  1 == bn(9223372036854775808'u64)
  doAssert cons(0, 0, 1) shr 65 == bn(9223372036854775808'u64)

block parsing:
  doAssert parseBignum("0") == bn(0)
  doAssert parseBignum("-0") == bn(0)
  doAssert parseBignum("1") == bn(1)
  doAssert parseBignum("-1") == bn(-1)
  doAssert parseBignum("123456") == bn(123456)
  doAssert parseBignum("-123456") == bn(-123456)

var d: array[39, Bignum] ## array of powers of 10
d[0] =  1'n
d[1] =  10'n
d[2] =  100'n
d[3] =  1000'n
d[4] =  10000'n
d[5] =  100000'n
d[6] =  1000000'n
d[7] =  10000000'n
d[8] =  100000000'n
d[9] =  1000000000'n
d[10] = 10000000000'n
d[11] = 100000000000'n
d[12] = 1000000000000'n
d[13] = 10000000000000'n
d[14] = 100000000000000'n
d[15] = 1000000000000000'n
d[16] = 10000000000000000'n
d[17] = 100000000000000000'n
d[18] = 1000000000000000000'n
d[19] = 10000000000000000000'n
d[20] = 100000000000000000000'n
d[21] = 1000000000000000000000'n
d[22] = 10000000000000000000000'n
d[23] = 100000000000000000000000'n
d[24] = 1000000000000000000000000'n
d[25] = 10000000000000000000000000'n
d[26] = 100000000000000000000000000'n
d[27] = 1000000000000000000000000000'n
d[28] = 10000000000000000000000000000'n
d[29] = 100000000000000000000000000000'n
d[30] = 1000000000000000000000000000000'n
d[31] = 10000000000000000000000000000000'n
d[32] = 100000000000000000000000000000000'n
d[33] = 1000000000000000000000000000000000'n
d[34] = 10000000000000000000000000000000000'n
d[35] = 100000000000000000000000000000000000'n
d[36] = 1000000000000000000000000000000000000'n
d[37] = 10000000000000000000000000000000000000'n
d[38] = 100000000000000000000000000000000000000'n

block add_sub_test:
  # test addition:
  var sum: Bignum
  for it in d.items:
    sum = sum + it

  doAssert sum == 111111111111111111111111111111111111111'n

  # test subtraction:
  for it in d.items:
    sum = sum - it

  doAssert sum == Zero

# test comparison, multiplication, and division with positive nubers:
for i, a in d.pairs:
  for j, b in d.pairs:
    doAssert(cmp(a, b) == cmp(i, j))
    if i + j < d.len:
      doAssert a * b == d[i + j]
    if i - j >= 0:
      doAssert a div b == d[i - j]

# test comparison, multiplication, and division with negative nubers:
for it in d.mitems:
  it = -it

for i, a in d.pairs:
  for j, b in d.pairs:
    doAssert(cmp(a, b) == -cmp(i, j))
    if i + j < d.len:
      doAssert a * b == -d[i + j]
    if i - j >= 0:
      doAssert a div b == -d[i - j]

block sign_test:
  # make sure the sign of quotients, remainders, and products is correct
  let
    a = 100'i64
    b = 13

  doAssert bignum(a) * bignum(0) == bignum(0)
  doAssert bignum(-a) * bignum(0) == bignum(0)

  template compare(a, b): bool =
    divMod(bignum(a), bignum(b)) == (bignum(a div b), bignum(a mod b))

  doAssert compare( a,  b)
  doAssert compare(-a,  b)
  doAssert compare(-a, -b)
  doAssert compare( a, -b)

  doAssert compare( b,  b)
  doAssert compare(-b,  b)
  doAssert compare(-b, -b)
  doAssert compare( b, -b)

  doAssert compare( b,  a)
  doAssert compare(-b,  a)
  doAssert compare(-b, -a)
  doAssert compare( b, -a)

# more tests for logical left and right shift:
let e = 70997106675279150998592376708984375'n
let rshifted = [
  # toHex(e shr 0), toHex(e shr 1), toHex(e shr 2), toHex(e shr 3), ...
  "000dac6d782d266a37300c32591eee37", "0006d636bc1693351b9806192c8f771b", "00036b1b5e0b499a8dcc030c9647bb8d", "0001b58daf05a4cd46e601864b23ddc6",
  "0000dac6d782d266a37300c32591eee3", "00006d636bc1693351b9806192c8f771", "000036b1b5e0b499a8dcc030c9647bb8", "00001b58daf05a4cd46e601864b23ddc",
  "00000dac6d782d266a37300c32591eee", "000006d636bc1693351b9806192c8f77", "0000036b1b5e0b499a8dcc030c9647bb", "000001b58daf05a4cd46e601864b23dd",
  "000000dac6d782d266a37300c32591ee", "0000006d636bc1693351b9806192c8f7", "00000036b1b5e0b499a8dcc030c9647b", "0000001b58daf05a4cd46e601864b23d",
  "0000000dac6d782d266a37300c32591e", "00000006d636bc1693351b9806192c8f", "000000036b1b5e0b499a8dcc030c9647", "00000001b58daf05a4cd46e601864b23",
  "00000000dac6d782d266a37300c32591", "000000006d636bc1693351b9806192c8", "0000000036b1b5e0b499a8dcc030c964", "000000001b58daf05a4cd46e601864b2",
  "000000000dac6d782d266a37300c3259", "0000000006d636bc1693351b9806192c", "00000000036b1b5e0b499a8dcc030c96", "0000000001b58daf05a4cd46e601864b",
  "0000000000dac6d782d266a37300c325", "00000000006d636bc1693351b9806192", "000000000036b1b5e0b499a8dcc030c9", "00000000001b58daf05a4cd46e601864",
  "00000000000dac6d782d266a37300c32", "000000000006d636bc1693351b980619", "0000000000036b1b5e0b499a8dcc030c", "000000000001b58daf05a4cd46e60186",
  "000000000000dac6d782d266a37300c3", "0000000000006d636bc1693351b98061", "00000000000036b1b5e0b499a8dcc030", "0000000000001b58daf05a4cd46e6018",
  "0000000000000dac6d782d266a37300c", "00000000000006d636bc1693351b9806", "000000000000036b1b5e0b499a8dcc03", "00000000000001b58daf05a4cd46e601",
  "00000000000000dac6d782d266a37300", "000000000000006d636bc1693351b980", "0000000000000036b1b5e0b499a8dcc0", "000000000000001b58daf05a4cd46e60",
  "000000000000000dac6d782d266a3730", "0000000000000006d636bc1693351b98", "00000000000000036b1b5e0b499a8dcc", "0000000000000001b58daf05a4cd46e6",
  "0000000000000000dac6d782d266a373", "00000000000000006d636bc1693351b9", "000000000000000036b1b5e0b499a8dc", "00000000000000001b58daf05a4cd46e",
  "00000000000000000dac6d782d266a37", "000000000000000006d636bc1693351b", "0000000000000000036b1b5e0b499a8d", "000000000000000001b58daf05a4cd46",
  "000000000000000000dac6d782d266a3", "0000000000000000006d636bc1693351", "00000000000000000036b1b5e0b499a8", "0000000000000000001b58daf05a4cd4",
  "0000000000000000000dac6d782d266a", "00000000000000000006d636bc169335", "000000000000000000036b1b5e0b499a", "00000000000000000001b58daf05a4cd",
  "00000000000000000000dac6d782d266", "000000000000000000006d636bc16933", "0000000000000000000036b1b5e0b499", "000000000000000000001b58daf05a4c",
  "000000000000000000000dac6d782d26", "0000000000000000000006d636bc1693", "00000000000000000000036b1b5e0b49", "0000000000000000000001b58daf05a4",
  "0000000000000000000000dac6d782d2", "00000000000000000000006d636bc169", "000000000000000000000036b1b5e0b4", "00000000000000000000001b58daf05a",
  "00000000000000000000000dac6d782d", "000000000000000000000006d636bc16", "0000000000000000000000036b1b5e0b", "000000000000000000000001b58daf05",
  "000000000000000000000000dac6d782", "0000000000000000000000006d636bc1", "00000000000000000000000036b1b5e0", "0000000000000000000000001b58daf0",
  "0000000000000000000000000dac6d78", "00000000000000000000000006d636bc", "000000000000000000000000036b1b5e", "00000000000000000000000001b58daf",
  "00000000000000000000000000dac6d7", "000000000000000000000000006d636b", "0000000000000000000000000036b1b5", "000000000000000000000000001b58da",
  "000000000000000000000000000dac6d", "0000000000000000000000000006d636", "00000000000000000000000000036b1b", "0000000000000000000000000001b58d",
  "0000000000000000000000000000dac6", "00000000000000000000000000006d63", "000000000000000000000000000036b1", "00000000000000000000000000001b58",
  "00000000000000000000000000000dac", "000000000000000000000000000006d6", "0000000000000000000000000000036b", "000000000000000000000000000001b5",
  "000000000000000000000000000000da", "0000000000000000000000000000006d", "00000000000000000000000000000036", "0000000000000000000000000000001b",
  "0000000000000000000000000000000d", "00000000000000000000000000000006", "00000000000000000000000000000003", "00000000000000000000000000000001",
  "00000000000000000000000000000000", "00000000000000000000000000000000", "00000000000000000000000000000000", "00000000000000000000000000000000",
  "00000000000000000000000000000000", "00000000000000000000000000000000", "00000000000000000000000000000000", "00000000000000000000000000000000",
  "00000000000000000000000000000000", "00000000000000000000000000000000", "00000000000000000000000000000000", "00000000000000000000000000000000",
]
let lshifted = [
  # toHex(e shl 0), toHex(e shl 1), toHex(e shl 2), toHex(e shl 3), ...
  "dac6d782d266a37300c32591eee37", "1b58daf05a4cd46e601864b23ddc6e", "36b1b5e0b499a8dcc030c9647bb8dc", "6d636bc1693351b9806192c8f771b8"
]

proc toHex(i: Bignum): string =
  var val = i
  while val != Zero:
    let (q, r) = udivMod(val, 16'n)
    result.insert $"0123456789abcdef"[r.toInt]
    val = q

proc pad(x: sink string): string =
  result = x
  for _ in result.len..<32:
    result.insert "0"

for i in 0 ..< 128:
  doAssert rshifted[i] == pad(toHex(e shr i))

  var lsh = lshifted[i mod 4]
  # append a zero for every 4 bit:
  for _ in 0..<(i div 4):
    lsh.add "0"
  doAssert lsh == toHex(e shl i)

block parse_stringify_roundtrip:
  template test(str: string): bool = $parseBignum(str) == str

  doAssert test("12345678987654321012345678987")
  doAssert test("0")
  # leading zeroes:
  doAssert $parseBignum("0001") == "1"
  doAssert $parseBignum("-0001") == "-1"
  doAssert $parseBignum("-0") == "0"
  # trailing zeroes:
  doAssert test("10")
  doAssert test("-10")
