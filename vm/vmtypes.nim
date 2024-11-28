## This module contains various functions for querying information about
## `TypeId`s and working with them in general.

type
  TypeId* = distinct uint32
    ## Identifies a procedure signature.

  TypeKind* = enum
    tkVoid
    tkInt
    tkFloat
    tkForeign

  VmType* = TypeKind # for backwards compatibility

  TypeEnv* = object
    ## Flat and data-oriented for the purpose of being easy to serialize and
    ## fast to operate on.
    types*: seq[Slice[uint32]]
      ## list of procedure signatures. A signature is a sequence of types,
      ## with a minimum length of 1. The actual types are stored separately in
      ## `params`
    params*: seq[VmType]

proc `==`*(a, b: TypeId): bool {.borrow.}

template `[]`*(e: TypeEnv, id: TypeId): Slice[uint32] =
  e.types[ord(id)]

iterator parameters*(e: TypeEnv, id: TypeId): (int, VmType) =
  ## Returns all parameters for procedure type `id`.
  var i = e[id].a + 1
  let fin = e[id].b
  while i <= fin:
    yield (int(i - e[id].a - 1), e.params[i])
    inc i

func numParams*(e: TypeEnv, id: TypeId): int =
  ## Returns the number of parameters the signature identified by `id` has.
  result = e[id].len - 1

func param*(e: TypeEnv, id: TypeId, i: Natural): VmType =
  ## The `i`th parameter's type.
  e.params[e[id].a + 1 + uint32(i)]

func returnType*(e: TypeEnv, id: TypeId): VmType =
  ## The return type of procedure `id`.
  e.params[e[id].a]

func add*(e: var TypeEnv, ret: VmType, params: openArray[VmType]): TypeId =
  ## Adds `desc` to the environment, returning the ID to later address it with.
  result = e.types.len.TypeId
  e.types.add(e.params.len.uint32 .. uint32(e.params.len + params.len))
  e.params.add ret
  e.params.add params
