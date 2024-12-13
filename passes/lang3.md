## L3 Language

```grammar
.extends lang2
```

`Blob` types are replaced with structured aggregate types. A `Record` is a
structure with sequentially layed out fields, a `Union` is a structure where
all fields use the same memory region, and an `Array` is a homogenous sequence
with a static number of elements.

```grammar
typedesc -= (Blob <int> <int>)
typedesc += (Record size:<int> align:<int> (Field <int> <type>)+)
          | (Union  size:<int> align:<int> <type>+)
          | (Array  size:<int> align:<int> count:<int> <type>)

type -= (Blob <int> <int>)
```

Aggregate types have a *derived* size and alignment. The derived size must
match the explicitly size specified on the type (which is there to speed up
processing), while the explicitly specified alignment may be a multiple of
the derived one.

Elements of aggregate values are addressed via `Path` expressions.

```grammar
path_idx ::= <int> | <expr>
path     ::= (Path <type> <local> <path_idx>+)
          |  (Path <type> (Deref <type> <expr>) <path_idx>+)
```

`Path` expressions function as l-value expressions.

```grammar
expr += (Addr <path>)
      | (Copy <path>)
stmt += (Asgn <path> <expr>)
```
