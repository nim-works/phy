## L30 Language

```grammar
.extends lang25
```

Instead of one flat list of statements, statements in a procedure can now be
nested:

```grammar
procdef -= (ProcDef <type_id> (Locals <type>*) (Stmts <stmt>+))
procdef += (ProcDef <type_id> (Locals <type>*) <single_stmt>)
```

The goto-based control-flow constructs are replaced with structured equivalents.

```grammar
single_stmt ::= (Stmts <stmt>+)
            |  <stmt>

choice -= (Choice <intVal> <goto>)
        | (Choice <floatVal> <goto>)
        | (Choice <intVal> <intVal> <goto>)
        | (Choice <floatVal> <floatVal> <goto>)

choice += (Choice <intVal> <single_stmt>)
        | (Choice <floatVal> <single_stmt>)

stmt -= (Join   <cont_name>)
      | (Except <cont_name> <local>)
      | <exit>
      | <goto>

stmt += (Block <single_stmt>)
      | (Loop <single_stmt>)
      | (If <value> <single_stmt> <single_stmt>?)
      | (Case <type> <simple> <choice>+)
      | (CheckedCall <proc> <value>*)
      | (CheckedCall <type> <value>+)
      | (CheckedCallAsgn <local> <proc> <value>*)
      | (CheckedCallAsgn <local> <type> <value>+)
      | (Return <value>?)
      | (Raise <value>)
      | (Unreachable)
```

*Future consideration:* If-then-else support could be removed, which would
reduce the IL's surface area and make translation slightly simpler.

`Break` is used to break out of an enclosing `Block`, `Loop`, `If`, or `Case`.
A depth value of '0' refers to the most enclosing block.

```grammar
stmt += (Break depth:<int>)
```

*Rationale:* allowing `Break` to target `If` and `Case` makes translation
simpler and removes the need for some `Block`s.
