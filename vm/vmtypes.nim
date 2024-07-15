## This module contains various functions for querying information about
## `TypeId`s and working with them in general.

type
  TypeId* = distinct uint32
    ## The unique ID of a `TypeId`. Internally, it's an index into a sequence

  TypeKind* = enum
    tkVoid
    tkInt
    tkFloat
    tkProc
    tkForeign

  VmType* = object
    ## Basic run-time type information (=RTTI). Flat in-memory representation
    ## so that it's easily serializable.
    kind*: TypeKind
    a*: uint32 ## meaning depends on the kind
    b*: uint32 ## meaning depends on the kind

  TypeEnv* = object
    ## Flat and data-oriented for the purpose of being easy to serialize and
    ## fast to operate on.
    types* {.requiresInit.}: seq[VmType]
    params*: seq[TypeId]

const
  VoidType* = TypeId(0)

proc `==`*(a, b: TypeId): bool {.borrow.}

proc initTypeEnv*(): TypeEnv =
  # setup the environment with a void type as the first element
  result = TypeEnv(types: @[VmType(kind: tkVoid)])

template `[]`*(e: TypeEnv, id: TypeId): VmType =
  e.types[ord(id)]

iterator parameters*(e: TypeEnv, id: TypeId): (int, TypeId) =
  ## Returns all parameters for procedure type `id`.
  var i = e[id].a + 1
  let fin = e[id].b
  while i < fin:
    yield (int(i - e[id].a), e.params[i])
    inc i

func param*(e: TypeEnv, id: TypeId, i: Natural): TypeId =
  ## The `i`th parameter's type.
  e.params[e[id].a + 1 + uint32(i)]

func returnType*(e: TypeEnv, id: TypeId): TypeId =
  ## The return type of procedure `id`.
  e.params[e[id].a]

func len*(typ: VmType): int {.inline.} =
  ## Number of types in the procedure signature.
  int(typ.b - typ.a)

func add*(e: var TypeEnv, desc: VmType): TypeId =
  ## Adds `desc` to the environment, returning the ID to later address it with.
  result = e.types.len.TypeId
  e.types.add(desc)
