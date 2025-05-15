## LPtr

```grammar
.extends lang0
```

Pointer types are introduced.

```grammar
type += (Ptr)
```

The pointer value representing a pointer that doesn't point anywhere is
represented by the `Nil` expression.

```grammar
expr += (Nil)
```

Pointer arithmetic is done using the `Offset` operation, which applies an
unsigned integer with the same byte-width as a pointer scaled by a positive,
non-zero constant value.

```grammar
expr += (Offset base:<expr> idx:<expr> scale:<intVal>)
```
