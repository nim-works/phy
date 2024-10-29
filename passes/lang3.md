## L3 Language

```grammar
.extends lang1
```

```grammar
field ::= (Field offset:<int> <type_id>)

type += (Record size:<int> align:<int> <field>+)
     |  (Union  size:<int> align:<int> <type_id>+)
     |  (Array  size:<int> count:<int> <type_id>)
```

The `Record`, `Union`, and `Array` types are only allowed for:
* array elements,
* record/union fields
* pointer dereference types

```grammar
dpath ::= (At    <dpath_elem> elem:<value>)
       |  (Field <dpath_elem> field:<int>)

dpath_elem ::= (Deref <type_id> <simple>)
            |  <path>
```

The content of locations of such types is accessed with *path expressions*.

```grammar
rvalue += (Addr <dpath>)
```

The `Addr` operation computes the address of the location named by the path.
