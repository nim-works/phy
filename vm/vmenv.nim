## Implements the data types making up the VM environment, as well as basic
## routines for interacting with it.

import
  std/[
    tables
  ],
  vm/[
    utils,
    vmalloc,
    vmspec,
    vmtypes
  ]

type
  PrgCtr* = uint32 ## program counter

  InstrType* = uint64
  Instr* = distinct InstrType

  ProcKind* = enum
    pkStub     ## a stub. Must be resolved first
    pkDefault  ## a normal procedure
    pkCallback ## redirected to a callback

  ProcIndex*   = distinct uint32
  ProcAddress* = distinct uint32

  ProcHeader* = object
    ## Stores the various information about a procedure, such as the type,
    ## locals, body, etc.
    kind*: ProcKind
    typ*: TypeId
      ## the procedure's type
    code*: Slice[PrgCtr]
      ## for callbacks, the callback index. Otherwise the slice of
      ## instructions
    locals*: HOslice[uint32]
      ## the types of the locals (can be empty)
    eh*: HOslice[uint32]
      ## the exception handler (EH) table slice associated with the proc
      ## (can be empty)

  Value* = distinct uint64
    ## Untyped 64-bit value representing a single value.

  ValueType* = enum
    vtInt   ## 64-bit integer (unknown signedness)
    vtFloat ## 64-bit float
    vtRef   ## foreign reference

  TypedValue* = object
    ## Value + type.
    typ*: ValueType
    val*: Value

  CallbackExitCode* = enum
    cecNothing # success; nothing is returned
    cecValue   # success; a value is returned
    cecRaise   # an exception is raised
    cecError   # fatal error occurred

  CallbackResult* = object
    ## Result of a VM callback.
    code*: CallbackExitCode
    value*: Value

  VmCallback* = proc(env: var VmEnv, args: openArray[Value],
                     cl: RootRef): CallbackResult {.nimcall, raises: [].}

  HandlerTableEntry* = tuple
    offset: uint32 ## instruction offset, relative to current proc start
    instr:  uint32 ## position of the EH instruction to execute

  EhInstr* = tuple
    ## Exception handling instruction. 4-byte in size.
    opcode: EhOpcode
    a: uint16 ## meaning depends on the opcode

  VmEnv* = object
    ## The total VM execution environment. An instance of this type represents
    ## a full VM instance.
    code*: seq[Instr]

    ehTable*: seq[HandlerTableEntry]
      ## stores the instruction-to-EH mappings. Used to look up the EH
      ## instruction to start exception handling with in case of a normal
      ## instruction raising
    ehCode*: seq[EhInstr]
      ## stores the instructions for the exception handling (EH) mechanism

    locals*: seq[ValueType]
    globals*: seq[TypedValue]
    constants*: seq[TypedValue]
    procs*: seq[ProcHeader]
    types*: TypeEnv

    callbacks*: seq[VmCallback]

    allocator*: VmAllocator
    # XXX: the allocator is located here for convenience, but splitting it from
    #      the environment would make sense; VmEnv would become copyable then

const
  instrOBits = 8  # opcode
  instrABits = 32
  instrBBits = 16
  instrCBits = 8

  # instruction shifts and masks
  instrOShift* = 0.InstrType
  instrAShift* = (instrOShift + instrOBits)
  instrBShift* = (instrAShift + instrABits)
  instrCShift* = (instrBShift + instrBBits)

  instrOMask*  = ((1.InstrType shl instrOBits) - 1)
  instrAMask*  = ((1.InstrType shl instrABits) - 1)
  instrBMask*  = ((1.InstrType shl instrBBits) - 1)
  instrCMask*  = ((1.InstrType shl instrCBits) - 1)

func `==`*(a, b: ProcIndex): bool {.borrow.}

func toAddr*(x: ProcIndex): ProcAddress {.inline.} =
  ProcAddress(uint32(x) + 1)

func deref*(x: ProcAddress): ProcIndex {.inline.} =
  ProcIndex(uint32(x) - 1)

template isNil*(x: ProcAddress): bool = uint32(x) == 0

template `[]`*(e: VmEnv, i: ProcIndex): ProcHeader =
  e.procs[uint32(i)]

proc initVm*(initial, maxHost: uint): VmEnv =
  ## Sets up and returns a VM execution environment.
  VmEnv(types: initTypeEnv(),
        allocator: initAllocator(initial, maxHost))

# instruction decoding
template opcode*(x: Instr): Opcode =
  Opcode(x.InstrType shr instrOShift and instrOMask)
template imm32*(x: Instr): int32 =
  cast[int32](x.InstrType shr instrAShift and instrAMask)
template imm32_16*(x: Instr): untyped =
  (cast[int32](x.InstrType shr instrAShift and instrAMask),
   cast[int16](x.InstrType shr instrBShift and instrBMask))
template imm32_8*(x: Instr): untyped =
  (cast[int32](x.InstrType shr instrAShift and instrAMask),
   cast[int8](x.InstrType shr instrCShift and instrCMask))
template imm8*(x: Instr): int8 =
  cast[int8](x.InstrType shr instrCShift and instrCMask)

# convenience value accessors
template uintVal*(x: Value): untyped  = cast[uint64](x)
template intVal*(x: Value): untyped   = cast[int64](x)
template floatVal*(x: Value): untyped = cast[float64](x)
template addrVal*(x: Value): untyped  = cast[VirtualAddr](x)

func `$`*(x: Value): string =
  "(uint: " & $x.uintVal & " int: " & $x.intVal & " float: " & $x.floatVal & ")"
