## L3 Language

```grammar
.extends lang1
```

There's no more unstructured `Blob` type:

```grammar
type -= (Blob <int>)
```

It's replaced with structured types:

```grammar
field ::= (Field offset:<int> <type_id>)

type += (Record size:<Int> <field>+)
     |  (Array size:<Int> count:<int> <type_id>)
```

As long as fields stay within the bounds of the record, they can use any
offset they want.

Both types can only be used as the type of:
* locals
* array elements
* record fields

The content of locations of such types is accessed with *path expressions*:

```grammar
path ::= (At    <path_elem> elem:<value>)
      |  (Field <path_elem> field:<int>)

path_elem ::= (Deref <type_id> <value>)
           |  <local>
           |  <path>
```

Path expressions are only allowed in a restricted set of contexts:

```grammar
rvalue += (Addr <path>)
value += (Copy <path>)
stmt += (Asgn <path> <value>)
```

Discarding an aggregate value (e.g., via `(Drop (Copy (Local 0)))`) is not
supported at this level.
