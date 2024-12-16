## L0 Language

The intermediate language immediately preceding VM bytecode. It has simple
abstractions over control-flow, stack allocation, reinterpretation and
conversions, and arithmetic operations, but generally stays close to VM
bytecode.

Procedures are split into continuations. They need to be ordered such
that all continuation exits (except for `Loop`) describe forward
jumps. One (and only one) continuation must be the "return" continuation.

```grammar
numtype  ::= (Int size:<int>)
          |  (UInt size:<int>)
          |  (Float size:<int>)
typedesc ::= (ProcTy (Void) <type>*)
          |  (ProcTy <type>+)
          |  <numtype>
type_id  ::= (Type <int>)
type     ::= <type_id>
          |  <numtype>
```

A type can be either *inlined* (anonymous) or *identified*. An *identified*
type is a type that has a name (in the form an integer ID), which is the only
way to refer to it. *Inlined* types have no name, and they're defined directly
where they're used (hence the name).

Only numeric types can be inlined.

```grammar
local ::= (Local <int>)
proc ::= (Proc <int>)

rvalue ::= (Load <type> <value>)
        |  (Addr (IntVal <int>))
        |  (Neg <type> <value>)
        |  (Add <type> <value> <value>)
        |  (Sub <type> <value> <value>)
        |  (Mul <type> <value> <value>)
        |  (Div <type> <value> <value>)
        |  (Mod <type> <value> <value>)
        |  (AddChck <type> <value> <value> <local>)
        |  (SubChck <type> <value> <value> <local>)
        |  (Not <value>)
        |  (Eq <type> <value> <value>)
        |  (Lt <type> <value> <value>)
        |  (Le <type> <value> <value>)
        |  (BitNot <type> <value>)
        |  (BitOr <type> <value> <value>)
        |  (BitAnd <type> <value> <value>)
        |  (BitXor <type> <value> <value>)
        |  (Shl <type> <value> <value>)
        |  (Shr <type> <value> <value>)
        |  (Reinterp <type> <type> <value>)
        |  (Conv <type> <type> <value>)
        |  (Call <proc> <value>*)
        |  (Call <type> <value>+)

intVal ::= (IntVal <int>)
floatVal ::= (FloatVal <float>)

simple ::= <intVal>
        |  <floatVal>
        |  (ProcVal <int>)
        |  (Copy <local>)
        |  (Copy (Global <int>))
value ::= <simple> | <rvalue>

cont_name ::= <int>

goto ::= (Continue <cont_name>)
err_goto ::= (Unwind)
          |  <goto>

choice ::= (Choice <intVal> <goto>)
        |  (Choice <floatVal> <goto>)
        |  (Choice <intVal> <intVal> <goto>)
        |  (Choice <floatVal> <floatVal> <goto>)

exit ::= <goto>
      |  (Continue <cont_name> <value>)
      |  (Loop <cont_name>)
      |  (Unreachable)
      |  (Raise <value> <err_goto>)
      |  (SelectBool <value> false:<goto> true:<goto>)
      |  (Select <type> <simple> <choice>+)
      |  (CheckedCall <proc> <value>* <goto> <err_goto>)
      |  (CheckedCall <type> <value>+ <goto> <err_goto>)
      |  (CheckedCallAsgn <local> <proc> <value>* <goto> <err_goto>)
      |  (CheckedCallAsgn <local> <type> <value>+ <goto> <err_goto>)

stmt ::= (Asgn <local> <value>)
      |  (Store <type> <value> <value>)
      |  (Clear <value> <value>)
      |  (Blit <value> <value> <value>)
      |  (Call <proc> <value>*)
      |  (Call <type> <value>+)
      |  (Drop <value>)

continuation ::= (Continuation (Params) stack:<int> <stmt>* <exit>)
              |  (Continuation (Params <type>?)) # return continuation
              |  (Except <local> stack:<int> <stmt>* <exit>)

procdef ::= (ProcDef <type_id> (Locals <type>*) (Continuations <continuation>+))
int_or_float ::= <intVal> | <floatVal>
globaldef ::= (GlobalDef <type> <int_or_float>)
```

### Foreign Procedures

```grammar
procdef += (Foreign <type_id> (StringVal <string>))
```

Foreign procedures are procedures that have an external implementation. How the
identifier is interpreted is up to the code generator / linker to decide.

### Module

All relevant entities (types, globals, and procedures) are stored under the
top-level node, in dedicated sections, to allow for easy and fast access to
them.

```grammar
module ::= (Module (TypeDefs <typedesc>*) (GlobalDefs <globaldef>*) (ProcDefs <procdef>*))
top ::= <module>
```
