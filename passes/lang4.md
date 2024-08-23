## L4 Language

```grammar
.extends lang3
```

There are no more procedure-wide locals:

```grammar
procdef -= (ProcDef <type_id> (Locals <type_id>*) (Continuations <continuation>+))
procdef += (ProcDef <type_id> (Continuations <continuation>+))
```

Instead, locals are per-continuation state. A continuation has parameters, and
a list of new locals it spawns:

```grammar
continuation -= (Continuation (Params) (Locals <local>*) <stmt>* <exit>)
              | (Except <local> (Locals <local>*) <stmt>* <exit>)
continuation += (Continuation (Params <type_id>*) (Locals <type_id>*) <stmt>* <exit>)
              | (Except       (Params <type_id>*) (Locals <type_id>*) <stmt>* <exit>)
```

A `Local` with an ID < *number of parameters* refers to a parameter --
all others refer to a spawned local.

Values are passed explicitly to continuations:

```grammar
cont_arg ::= (Move <local>)   # move the value
          |  (Rename <local>) # the identity (read, address) must stay the same
```

Every jump to another `Continuation` must specify which locals are moved
across; arity and types need to match those of the target continuation:

```grammar
exit -= (Continue <cont_name> <value>)
      | (Loop <cont_name>)

exit += (Continue <cont_name> <value> (List <cont_arg>*))
      | (Loop <cont_name> (List <cont_arg>*))

goto -= (Continue <cont_name>)
goto += (Continue <cont_name> (List <cont_arg>*))
```

There are no `CheckedCallAsgn`. Checked calls that return something use
`CheckedCall`s. They cannot pass something directly to the exit continuation.

```grammar
exit -= (CheckedCallAsgn <local> <proc> <value>* <goto> <err_goto>)
      | (CheckedCallAsgn <local> <type_id> <value>+ <goto> <err_goto>)
```

Exits via exceptional control-flow always pass the exception to the first
`Continuation` parameter.
