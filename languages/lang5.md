## L5 Language

```grammar
.extends lang4
```

Instead of flat `Path` expressions, records and unions are accessed via the
`Field` and arrays via the `At` lvalue expression.

```grammar

path -= (Path <type> <local> <path_idx>+)
      | (Path <type> (Deref <type> <expr>) <path_idx>+)
path += (Field <path_elem> <int>)
      | (At    <path_elem> <expr>)

path_elem ::= (Deref <type> <expr>) # a path root
           |  <local>               # also a path root
           |  <path>
```
