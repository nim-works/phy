## L1 Language

```grammar
.extends lang0
```

Numeric types can be identified types and identified types can be used in all
places where types are expected.

```grammar
typedesc += <numtype>
type += <type_id>
```

`Blob` types exist, but they're not yet allowed to be used in any context. The
`Blob` type represents sized untyped memory that has an alignment requirement.
The memory address of a blob value must be a multiple of its requested
alignment.

```grammar
typedesc += (Blob size:<int> align:<int>)
type     += (Blob size:<int> align:<int>)
```
