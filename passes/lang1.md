## L1 Language

```grammar
.extends lang0
```

```grammar
procdef -= (ProcDef <type_id> stack:<int> (Locals <type_id>*) (List <bblock>+))
procdef += (ProcDef <type_id> stack:<int> (List <bblock>+))
```

```grammar
bblock -= (Block (Params) <stmt>* <exit>)
        | (Except <local> <stmt>* <exit>)
bblock += (Block (Params <type_id>*) (Locals <type_id>*) <stmt>* <exit>)
        | (Except (Params <type_id>*) (Locals <type_id>*) <stmt>* <exit>)
```

Locals use the SSA form (they have one static assignment, which dominates all
usages) and they're passed between blocks via block parameters. There are no
critical edges.

All basic-block locals *must* be assigned to once, but they're not required to
be used.

```grammar
local += (Param <int>)
```

`Param` is used to refer to basic-block parameters.

```grammar
exit -= (Loop <block_name>)
exit += (Loop <block_name> (List <local>*))

goto -= (Goto <block_name>)
goto += (Goto <block_name> (List <local>*))
```

The locals specified as block arguments are *moved*, meaning that there must
be no duplicates in an argument list.
