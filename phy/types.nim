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

  SemType* = object
    ## Represent a source-language type. The "Sem" prefix is to not have it
    ## name conflicts with other types named `Type`.
    kind*: TypeKind

proc errorType*(): SemType {.inline.} =
  SemType(kind: tkError)

proc prim*(kind: TypeKind): SemType {.inline.} =
  ## Returns the primitive type with the given kind.
  SemType(kind: kind)
