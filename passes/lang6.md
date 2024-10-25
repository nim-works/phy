## L4 Language

```grammar
.extends lang4
```

Aggregate types can be used for locals, with locals being usable as path
roots.

```grammar
local_path ::= (At <local_path_elem> <value>)
            |  (Field <local_path_elem> field:<int>)

local_path_elem ::= <local_path> | <local>

value += (Copy <local_path>)
       | (Move <local_path>)
```

Aggregate locals also use the SSA form, which means that an assignment of a
field or array element must dominate all direct or indirect usages thereof.
Dynamic array indexing counts as an indirect usage.

```grammar
stmt += (Asgn <local_path> <value>)
```
