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
unsigned integer with the same byte-width as a pointer scaled by a non-zero,
positive constant value.

```grammar
expr += (Offset ptr:<expr> by:<expr> scale:<intVal>)
```
