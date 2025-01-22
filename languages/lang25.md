## L25 Language

```grammar
.extends lang5
```

Procedure bodies are not subdivided into basic-blocks, but instead consist of
a list of statements:

```grammar
procdef -= (ProcDef <type_id> (Locals <type>*) (List <bblock>+))
procdef += (ProcDef <type_id> (Params <local>*) (Locals <type>*) (Stmts <stmt>+))
```

### Control Flow

Control-flow statements can now appear in a normal statement context:

```grammar
exit -= (CheckedCall <proc> <expr>* <goto> <err_goto>)
      | (CheckedCall <type_id> <expr>+ <goto> <err_goto>)

exit += (CheckedCall <proc> <expr>* <err_goto>)
      | (CheckedCall <type_id> <expr>+ <err_goto>)
      | (CheckedCallAsgn <local> <proc> <expr>* <err_goto>)
      | (CheckedCallAsgn <local> <type_id> <expr>+ <err_goto>)

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
