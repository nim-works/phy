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
continuation += (Continuation (Params <type_id>*) (Locals <type_id>*) <stmt>* <exit>)
```

There are no special `Except` continuations:

```grammar
continuation -= (Except <local> (Locals <local>*) <stmt>* <exit>)
```

A `Local` with an ID < *number of parameters* refers to a parameter --
all others refer to a spawned local.

Values are passed explicitly to continuations:

```grammar
cont_arg ::= (Move <local>)   # move the value
          |  (Rename <local>) # the identity (read, address) must stay the same
```

Every jump to another `Continuation`s must specify which locals are moved
across and which ones are dropped/killed; arity and types need to match the
target continuation:

```grammar
exit -= (Continue <cont_name> <value>)
      | (Loop <cont_name>)

exit += (Continue <cont_name> <value> (List <cont_arg>*) drop:(List <local>*))
      | (Loop <cont_name> (List <cont_arg>*) drop:(List <local>*))

goto -= (Continue <cont_name>)
goto += (Continue <cont_name> (List <cont_arg>*) drop:(List <local>*))
```

There are no `CheckedCallAsgn`. Checked calls that return something use
`CheckedCall`s.

```grammar
exit -= (CheckedCallAsgn <local> <proc> <value>* <goto> <err_goto>)
      | (CheckedCallAsgn <local> <type_id> <value>+ <goto> <err_goto>)
```

Exits via exceptional control-flow always pass the exception to the first
`Continuation` parameter.
