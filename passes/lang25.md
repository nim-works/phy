## L25 Language

```grammar
.extends lang4
```

Procedures are no subdivided into continuations, but instead consist of a list
of statements:

```grammar
procdef -= (ProcDef <type_id> (Continuations <continuation>+))
procdef += (ProcDef <type_id> (Locals <type>*) (Stmts <stmt>+))
```

### Control Flow

Control-flow statements can now appear in normal statement contexts:

```grammar
exit -= (Continue <cont_name> <value> (List <cont_arg>*))
      | (Loop <cont_name> (List <cont_arg>*))
      | (Raise <value> <err_goto>)
      | (CheckedCall <proc> <value>* <goto> <err_goto>)
      | (CheckedCall <type> <value>+ <goto> <err_goto>)

exit += (Continue <cont_name> <value>)
      | (Loop <cont_name>)
      | (Return <value>?)
      | (Raise <value> <err_goto>)
      | (CheckedCall <proc> <value>* <err_goto>)
      | (CheckedCall <type> <value>+ <err_goto>)
      | (CheckedCallAsgn <local> <proc> <value>* <err_goto>)
      | (CheckedCallAsgn <local> <type> <value>+ <err_goto>)

goto -= (Continue <cont_name> (List <cont_arg>*))
goto += (Continue <cont_name>)

stmt += <goto>
      | <exit>
```

```grammar
stmt += (Join label:<cont_name>)
```

A `Join` statement represents the destination of a non-exceptional control-
flow statement. Control-flow is allowed to reach a `Join` statement without a
jump. Labels can be arbitrary numbers.

```grammar
stmt += (Except label:<cont_name> <local>)
```

An `Except` statement represents the jump target for exceptional control-flow.
Control-flow is *not* allowed to reach an `Except` without a jump.

A `Loop` statement *must* be backward control-flow; jumps from outside a loop
to inside of it are disallowed. For example:
```
(Join 0)
(Join 1)
...
(Loop 0)
...
(Loop 1)
```
is illegal.

All other jumps *must* describe forward control-flow, and a procedure body must
end in a control-flow statement.
