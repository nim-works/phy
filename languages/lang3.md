## L3 Language

```grammar
.extends lang2
```

`Blob` types are replaced with structured aggregate types. A `Record` is a
structure with sequentially layed out fields, a `Union` is a structure where
all fields use the same memory region, and an `Array` is a homogenous sequence
with a static number of elements.

Same as with `Blob` types, aggregate types are not allowed as parameter and
return value types.

```grammar
typedesc -= (Blob <int> <int>)
typedesc += (Record size:<int> align:<int> (Field <int> <type>)+)
          | (Union  size:<int> align:<int> <type>+)
          | (Array  size:<int> align:<int> count:<int> <type>)

type -= (Blob <int> <int>)
```

Aggregate types have a *derived* alignment, which is that of their most
aligned element type. The explicitly specified alignment must be equal to
or a multiple of the derived alignment and a power of two.

The alignment for numeric types is equal to their size.

Aggregate types also have a *derived* and *padded* size. The *padded* size
is the *derived* size rounded up such that it's a multiple of the specified
alignment. The *derived* size is computed as follows:
* `Record`: offset of the last field + *padded* size of the last field's type
* `Union`: *padded* size of the largest element type
* `Array`: *padded* element type size * number of elements

The explicitly specified size on the type (which is there to speed up
processing), must be equal to the *padded* size.

For `Record` types, the specified field offsets must be ascending and a
multiple of the respective field type's alignment requirement.


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

Pointer arithmetic is not allowed anymore.

```grammar
expr -= (Offset <expr> <expr> <intVal>)
```
