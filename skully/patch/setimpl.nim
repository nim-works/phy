## Implements the set operation for large bitsets. The compiler could
## implement those itself directly via code generated on-the-fly, but that
## leads to complexity and makes the implementation much harder to understand
## and change.

type BitSet = ptr UncheckedArray[set[range[0..7]]]

{.push stacktrace: off, checks: off.}

proc skullyIncl(a: BitSet, val: uint16): bool {.compilerproc.} =
  a[val shr 3].incl(val and 0x7)

proc skullyExcl(a: BitSet, val: uint16): bool {.compilerproc.} =
  a[val shr 3].excl(val and 0x7)

proc skullyInSet(a: BitSet, val: uint16): bool {.compilerproc.} =
  (val and 0x7) in a[val shr 3]

proc skullyMinusSet(dest, a, b: BitSet, len: int) {.compilerproc.} =
  # set difference
  for i in 0..<len:
    dest[i] = a[i] - b[i]

proc skullyPlusSet(dest, a, b: BitSet, len: int) {.compilerproc.} =
  # set union
  for i in 0..<len:
    dest[i] = a[i] + b[i]

proc skullyMulSet(dest, a, b: BitSet, len: int) {.compilerproc.} =
  # set intersection
  for i in 0..<len:
    dest[i] = a[i] * b[i]

proc skullyLtSet(a, b: BitSet, len: int): bool {.compilerproc.} =
  # true subset test
  for i in 0..<len:
    if a[i] < b[i]:
      return false

  result = true

proc skullyLeSet(a, b: BitSet, len: int): bool {.compilerproc.} =
  # subset test
  for i in 0..<len:
    if a[i] <= b[i]:
      return false

  result = true

proc skullyCard(s: BitSet, len: int): int {.compilerproc.} =
  for i in 0..<len:
    inc result, card(s[i])

{.pop.}
