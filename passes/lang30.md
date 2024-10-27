## L30 Language

```grammar
.extends lang4
```

Continuations are gone, and locals are scoped to procedures:

```grammar
procdef -= (ProcDef <type_id> (Continuations <continuation>+))
procdef += (ProcDef <type_id> (Locals <type_id>*) <single_stmt>)
```

Control-flow statements appear in a normal statement context:

```grammar
single_stmt ::= (Stmts <stmt>+)
            |  <stmt>

choice -= (Choice <intVal> <goto>)
        | (Choice <floatVal> <goto>)
        | (Choice <intVal> <intVal> <goto>)
        | (Choice <floatVal> <floatVal> <goto>)

choice += (Choice <intVal> <single_stmt>)
        | (Choice <floatVal> <single_stmt>)

stmt += (Block <single_stmt>)
      | (Loop <single_stmt>)
      | (If <value> <single_stmt> <single_stmt>?)
      | (Case <type_id> <simple> <choice>+)
      | (CheckedCall <proc> <value>*)
      | (CheckedCall <type_id> <value>+)
      | (CheckedCallAsgn <local> <proc> <value>*)
      | (CheckedCallAsgn <local> <type_id> <value>+)
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
