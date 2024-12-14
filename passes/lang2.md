## L2 Language

```grammar
.extends lang1
```

Procedures no longer specify the size of their stack frame.

```grammar
procdef -= (ProcDef <type_id> <int> (Locals <type>*) (List <bblock>+))
procdef += (ProcDef <type_id> (Locals <type>*) (List <bblock>+))
```

In addition, locals may be of `Blob` type. Blob locals may also have
their address taken (locals of numeric type must not). Parameters
and return values must not be of `Blob` type.

```grammar
expr += (Addr <local>)
```
