## L0 Language

The intermediate language immediately preceding VM bytecode. It has simple
abstractions over control-flow, stack allocation, reinterpretation and
conversions, and arithmetic operations, but generally stays close to VM
bytecode.

```grammar
numtype  ::= (Int size:<int>)
          |  (UInt size:<int>)
          |  (Float size:<int>)
typedesc ::= (ProcTy (Void) <type>*)
          |  (ProcTy <type>+)
type_id  ::= (Type <int>)
type     ::= <numtype>
```

A type can be either *inlined* (anonymous) or *identified*. An *identified*
type is a type that has a name (in the form an integer ID), which is the only
way to refer to it. *Inlined* types have no name, and they're defined directly
where they're used (hence the name).

Only numeric types can be inlined.

```grammar
local   ::= (Local <int>)
proc    ::= (Proc <int>)

arith  ::= (Neg <type> <expr>)
        |  (Add <type> <expr> <expr>)
        |  (Sub <type> <expr> <expr>)
        |  (Mul <type> <expr> <expr>)
        |  (Div <type> <expr> <expr>)
        |  (Mod <type> <expr> <expr>)
        |  (AddChck <type> <expr> <expr> <local>)
        |  (SubChck <type> <expr> <expr> <local>)
        |  (MulChck <type> <expr> <expr> <local>)
        |  (Not <expr>)
        |  (Eq <type> <expr> <expr>)
        |  (Lt <type> <expr> <expr>)
        |  (Le <type> <expr> <expr>)
        |  (BitNot <type> <expr>)
        |  (BitOr  <type> <expr> <expr>)
        |  (BitAnd <type> <expr> <expr>)
        |  (BitXor <type> <expr> <expr>)
        |  (Shl <type> <expr> <expr>)
        |  (Shr <type> <expr> <expr>)

conv   ::= (Reinterp <type> <type> <expr>) # bit casting (between numeric types)
        |  (Conv     <type> <type> <expr>) # int-to-float conversion and vice versa
        |  (Zext     <type> <type> <expr>) # zero extension (integer only)
        |  (Sext     <type> <type> <expr>) # sign extension (integer only)
        |  (Trunc    <type> <type> <expr>) # integer truncation
        |  (Demote   <type> <type> <expr>) # larger float to smaller float demotion
        |  (Promote  <type> <type> <expr>) # smaller float to larger float promotion

memops ::= (Load <type> <expr>)

call   ::= (Call <proc> <expr>*)
        |  (Call <type_id> <expr>+)

intVal   ::= (IntVal <int>)
floatVal ::= (FloatVal <float>)

simple ::= <intVal>
        |  <floatVal>
        |  (ProcVal <int>)
        |  (Copy <local>)
        |  (Copy (Global <int>))
expr   ::= <simple>
        |  <arith>
        |  <conv>
        |  <memops>
        |  <call>

block_name ::= <int>

goto     ::= (Goto <block_name>)
err_goto ::= (Unwind)
          |  <goto>

choice ::= (Choice <intVal> <goto>)
        |  (Choice <floatVal> <goto>)
        |  (Choice <intVal> <intVal> <goto>)
        |  (Choice <floatVal> <floatVal> <goto>)

exit ::= <goto>
      |  (Return <expr>?)
      |  (Loop <block_name>)
      |  (Unreachable)
      |  (Raise <expr> <err_goto>)
      |  (Branch <expr> false:<goto> true:<goto>)
      |  (Select <type> <simple> <choice>+)
      |  (CheckedCall <proc> <expr>* <goto> <err_goto>)
      |  (CheckedCall <type_id> <expr>+ <goto> <err_goto>)
      |  (CheckedCallAsgn <local> <proc> <expr>* <goto> <err_goto>)
      |  (CheckedCallAsgn <local> <type_id> <expr>+ <goto> <err_goto>)

stmt ::= (Asgn <local> <expr>)
      |  (Store <type> <expr> <expr>)
      |  (Clear <expr> <expr>)
      |  (Blit <expr> <expr> <expr>)
      |  (Drop <expr>)
      |  <call>

bblock ::= (Block  (Params <local>*) <stmt>* <exit>)
        |  (Except (Params <local>)  <stmt>* <exit>)

dataInit   ::= (Data align:<int> size:<int>)
            |  (Data align:<int> content:(StringVal <string>))
globalInit ::= <dataInit> | <intVal> | <floatVal>
globaldef  ::= (GlobalDef <type> <globalInit>)
```

```grammar
procdef ::= (ProcDef <type_id> stack:<int> (Locals <type>*) (List <bblock>+))
```

Procedures are split into basic blocks. They need to be ordered such that
blocks come before the block they jump to (except for via `Loop` exits).
The first block is the entry block.

Only the entry `Block` may use block parameters. If `stack` is greater than 0,
the entry block must have `N` + 1 parameters (where `N` is the number of
parameter specified by the proc signature), otherwise it must have `N`
parameters. The entry block parameters specify which locals the procedure
arguments are stored in on procedure entry.

If `stack` is greater than 0, `stack` bytes are allocated from the stack on
procedure entry, and the frame pointer is stored in the local specified last
in the entry parameter block parameter list.

### Imported Procedures

```grammar
procdef += (Import typ:<type_id> name:(StringVal <string>))
```

Procedure imports declare procedures whose implementation is provided
externally. The `name` provides the interface name that the implementation is
provided under, and `typ` must be equal to the signature type of the
implementation.

### Exports

```grammar
export_id ::= (Proc <int>)
           |  (Global <int>)
export    ::= (Export name:(StringVal <string>) id:<export_id>)
```

An export makes a procedure or global variable available to the outside under
the given `name`.

### Module

All relevant entities (types, globals, procedures, and exports) are stored
under the top-level node, in dedicated sections, to allow for easy and fast
access to them.

```grammar
module ::= (Module (TypeDefs <typedesc>*) (GlobalDefs <globaldef>*) (ProcDefs <procdef>*) (List <export>+)?)
top ::= <module>
```
