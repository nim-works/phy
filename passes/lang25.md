## L25 Language

```grammar
.extends lang7
```

Procedures are no subdivided into continuations, but instead consist of a list
of statements:

```grammar
procdef -= (ProcDef <type_id> (List <type_id>*) (List <bblock>+))
procdef += (ProcDef <type_id> (Locals <type_id>*) (Stmts <stmt>+))
```

### Control Flow

Control-flow statements can now appear in normal statement contexts:

```grammar
exit -= (Loop <block_name> (List <local>*))
      | (Raise <value> <err_goto>)
      | (CheckedCall <proc> <value>* <goto> <err_goto>)
      | (CheckedCall <type_id> <value>+ <goto> <err_goto>)

exit += (Goto <block_name>)
      | (Loop <block_name>)
      | (Raise <value> <err_goto>)
      | (CheckedCall <proc> <value>* <err_goto>)
      | (CheckedCall <type_id> <value>+ <err_goto>)
      | (CheckedCallAsgn <local> <proc> <value>* <err_goto>)
      | (CheckedCallAsgn <local> <type_id> <value>+ <err_goto>)

goto -= (Goto <block_name> (List <local>*))
goto += (Goto <block_name>)

stmt += <goto>
      | <exit>
```

```grammar
stmt += (Join label:<block_name>)
```

A `Join` statement represents the destination of a non-exceptional control-
flow statement. Control-flow is allowed to reach a `Join` statement without a
jump. Labels can be arbitrary numbers.

```grammar
stmt += (Except label:<block_name> <local>)
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
