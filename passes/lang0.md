## L0 Language

The intermediate language immediately preceding VM bytecode. It has simple
abstractions over control-flow, stack allocation, reinterpretation and
conversions, and arithmetic operations, but generally stays close to VM
bytecode.

Procedures are split into continuations. They need to be ordered such
that all continuation exits (except for `Loop`) describe forward
jumps. One (and only one) continuation must be the "return" continuation.

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
        |  (Addr (IntVal <int>))
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
        |  (Copy (Global <int>))
value ::= <simple> | <rvalue>

cont_name ::= <int>

goto ::= (Continue <cont_name>)
err_goto ::= (Unwind)
          |  (List (Continue <cont_name>)* (Unwind)?)

choice ::= (Choice <intVal> <goto>)
        |  (Choice <floatVal> <goto>)
        |  (Choice <intVal> <intVal> <goto>)
        |  (Choice <floatVal> <floatVal> <goto>)

exit ::= (Continue)
      |  (Continue <cont_name>)
      |  (Continue <cont_name> <value>)
      |  (Enter <cont_name> <cont_name>)
      |  (Leave <cont_name>)
      |  (Loop <cont_name>)
      |  (Unreachable)
      |  (Raise <value> <cont_name>)
      |  (SelectBool <value> false:<goto> true:<goto>)
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

continuation ::= (Continuation (Params) stack:<int> <stmt>* <exit>)
              |  (Continuation (Params <type_id>?)) # return continuation
              |  (Subroutine (Params) stack:<int> <stmt>* <exit>)
              |  (Except <local> stack:<int> <stmt>* <exit>)

procdef ::= (ProcDef <type_id> (Locals <type_id>*) (Continuations <continuation>+))
```

### Module

All relevant entities (types, globals, and procedures) are stored under the
top-level node, in dedicated sections, to allow for easy and fast access to
them.

```grammar
module ::= (Module (TypeDefs <type>*) (GlobalDefs <type_id>*) (ProcDefs <procdef>*))
```
