## Provides the enum types for the various opcodes of the VM.

type
  Opcode* = enum
    opcNop

    # stack manipluation
    opcDrop       ## x:any
    opcDup        ## x:X -> X X
    opcSwap       ## a:A b:B -> B A

    # constants and immediate values
    opcLdConst    ## idx:imm32   -> int|float
    opcLdImmInt   ## val:imm32   -> int
    opcLdImmFloat ## val:float32 -> float

    # locals and globals
    opcGetLocal   ## idx:imm32 -> any
    opcSetLocal   ## x:X idx:imm32 -> X
    opcPopLocal   ## x:any idx:imm32
    opcGetGlobal  ## idx:imm32 -> any

    # integer arithmetic operations
    opcAddImm     ## val:int val:imm32
    opcAddInt     ## a:int b:int -> int
    opcSubInt     ## a:int b:int -> int
    opcMulInt     ## a:int b:int -> int
    opcDivInt     ## a:int b:int -> int
    opcDivU       ## a:int b:int -> int
    opcModInt     ## a:int b:int -> int
    opcModU       ## a:int b:int -> int
    opcNegInt     ## a:int       -> int
    opcOffset     ## base:int idx:int mul:imm32 -> int

    # checked signed integer arithmetic
    opcAddChck      ## a:int b:int width:imm8 -> res:int of:int
    opcSubChck      ## a:int b:int width:imm8 -> res:int of:int
    # TODO: consider adding checked integer multiplication

    # bit operations
    opcBitNot     ## a:int -> int
    opcBitAnd     ## a:int b:int -> int
    opcBitOr      ## a:int b:int -> int
    opcBitXor     ## a:int b:int -> int
    opcShr        ## a:int b:int -> int
    opcAshr       ## a:int b:int -> int
    opcShl        ## a:int b:int -> int
    opcMask       ## a:int bits:imm8
    opcSignExtend ## val:int width:imm8 -> int

    # float arithmetic
    opcAddFloat   ## a:float b:float -> float
    opcSubFloat   ## a:float b:float -> float
    opcMulFloat   ## a:float b:float -> float
    opcDivFloat   ## a:float b:float -> float
    opcNegFloat   ## a:float         -> float

    # boolean operations
    opcNot        ## a:int       -> int
    opcEqInt      ## a:int b:int -> int
    opcLtInt      ## a:int b:int -> int
    opcLeInt      ## a:int b:int -> int
    opcLtu        ## a:int b:int -> int
    opcLeu        ## a:int b:int -> int
    opcEqFloat    ## a:float b:float -> int
    opcLtFloat    ## a:float b:float -> int
    opcLeFloat    ## a:float b:float -> int

    # conversions
    opcUIntToFloat ## val:int   width:imm8 -> float
    opcFloatToUint ## val:float width:imm8 -> int
    opcSIntToFloat ## val:int   width:imm8 -> float
    opcFloatToSInt ## val:float width:imm8 -> int
    opcReinterpF32 ## val:int   -> float
    opcReinterpF64 ## val:int   -> float
    opcReinterpI32 ## val:float -> int
    opcReinterpI64 ## val:float -> int

    # memory operations
    opcLdInt8     ## addr:int offset:imm32
    opcLdInt16    ## addr:int offset:imm32
    opcLdInt32    ## addr:int offset:imm32
    opcLdInt64    ## addr:int offset:imm32

    opcLdFlt32    ## addr:int offset:imm32
    opcLdFlt64    ## addr:int offset:imm32

    opcWrInt8     ## addr:int offset:imm32
    opcWrInt16    ## addr:int offset:imm32
    opcWrInt32    ## addr:int offset:imm32
    opcWrInt64    ## addr:int offset:imm32
    opcWrFlt32    ## addr:int offset:imm32
    opcWrFlt64    ## addr:int offset:imm32

    opcWrRef      ## addr:int offset:imm32

    opcMemCopy    ## src:int dst:int len:int
    opcMemClear   ## dst:int len:int

    # control-flow operations
    opcJmp        ## target:imm32
    opcBranch     ## cond:int target:imm32 invert:imm8
    opcRet        ## val:any|none
    opcRaise      ## val:int
    opcCall       ## callee:imm32 num:imm16
    opcIndCall    ## callee:int typ:imm32 num:imm16
    opcIndCallCl  ## callee:int typ:imm32 num:imm16
    opcExcept     ## val:int

    # sub-routines
    opcBegin
    opcEnd
    opcEnter      ## target:imm32 num:imm16
    opcLeave      ## target:imm32 num:imm16

    # memory management
    opcStackAlloc ## size:imm32
    opcStackFree  ## size:imm32
    opcGrow       ## to:int

    opcYield      ## args:imm32 reason:imm8

  EhOpcode* = enum
    ehoExcept     ## enter an exception handler
    ehoSubroutine ## enter a subroutine
    ehoNext       ## forward jump to another EH instruction
    ehoEnd        ## end of current EH thread
