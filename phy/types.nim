## Implements types and procedures for representing and working with the
## source-language types.

type
  TypeKind* = enum
    tkError
    tkVoid
    tkUnit
    tkBool
    tkInt
    tkFloat
