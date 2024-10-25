## L0 Language

The intermediate language immediately preceding VM bytecode. It has simple
abstractions over control-flow, stack allocation, reinterpretation and
conversions, and arithmetic operations, but generally stays close to VM
bytecode.

```grammar
type_id ::= (Type <int>)
type ::= (Int size:<int>)
      |  (UInt size:<int>)
      |  (Float size:<int>)
      |  (ProcTy (Void) <type_id>*)
      |  (ProcTy <type_id>+)

local ::= (Local <int>)
proc ::= (Proc <int>)

rvalue ::= (Load <type_id> <value>)
        |  (Neg <type_id> <value>)
        |  (Add <type_id> <value> <value>)
        |  (Sub <type_id> <value> <value>)
        |  (Mul <type_id> <value> <value>)
        |  (Div <type_id> <value> <value>)
        |  (Mod <type_id> <value> <value>)
        |  (AddChck <type_id> <value> <value> <local>)
        |  (SubChck <type_id> <value> <value> <local>)
        |  (Not <value>)
        |  (Eq <type_id> <value> <value>)
        |  (Lt <type_id> <value> <value>)
        |  (Le <type_id> <value> <value>)
        |  (BitNot <type_id> <value>)
        |  (BitOr <type_id> <value> <value>)
        |  (BitAnd <type_id> <value> <value>)
        |  (BitXor <type_id> <value> <value>)
        |  (Shl <type_id> <value> <value>)
        |  (Shr <type_id> <value> <value>)
        |  (Reinterp <type_id> <type_id> <value>)
        |  (Conv <type_id> <type_id> <value>)
        |  (Call <proc> <value>*)
        |  (Call <type_id> <value>+)

intVal ::= (IntVal <int>)
floatVal ::= (FloatVal <float>)

simple ::= <intVal>
        |  <floatVal>
        |  (ProcVal <int>)
        |  (Copy <local>)
        |  (Move <local>)
        |  (Copy (Global <int>))
value ::= <simple> | <rvalue>

block_name ::= <int>

goto ::= (Goto <block_name>)
err_goto ::= (Unwind)
          |  <goto>

choice ::= (Choice <intVal> <goto>)
        |  (Choice <floatVal> <goto>)
        |  (Choice <intVal> <intVal> <goto>)
        |  (Choice <floatVal> <floatVal> <goto>)

exit ::= <goto>
      |  (Return <value>?)
      |  (Loop <block_name>)
      |  (Unreachable)
      |  (Raise <value> <err_goto>)
      |  (Branch <value> false:<goto> true:<goto>)
      |  (Select <type_id> <simple> <choice>+)
      |  (CheckedCall <proc> <value>* <goto> <err_goto>)
      |  (CheckedCall <type_id> <value>+ <goto> <err_goto>)
      |  (CheckedCallAsgn <local> <proc> <value>* <goto> <err_goto>)
      |  (CheckedCallAsgn <local> <type_id> <value>+ <goto> <err_goto>)

stmt ::= (Asgn <local> <value>)
      |  (Store <type_id> <value> <value>)
      |  (Clear <value> <value>)
      |  (Copy <value> <value> <value>)
      |  (Call <proc> <value>*)
      |  (Call <type_id> <value>+)
      |  (Drop <value>)

bblock ::= (Block (Params) <stmt>* <exit>)
        |  (Except <local> <stmt>* <exit>)

globaldef ::= <intVal> | <floatVal>
```

```grammar
procdef ::= (ProcDef <type_id> stack:<int> (Locals <type_id>*) (List <bblock>+))
```

Procedures are split into basic blocks. They need to be ordered such that
blocks come before the block they jump to (except for via `Loop` exits).
The first block is the entry block.

If `stack` is greater than 0, `stack` bytes are allocated from the stack, and
the frame pointer is stored in the `n`-th local, where `n` is the number of
parameters + 1 (the local must exist).

### Module

All relevant entities (types, globals, and procedures) are stored under the
top-level node, in dedicated sections, to allow for easy and fast access to
them.

```grammar
module ::= (Module (TypeDefs <type>*) (GlobalDefs <globaldef>*) (ProcDefs <procdef>*))
top ::= <module>
```
