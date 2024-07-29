## L1 Language

```grammar
.extends lang0
```

Blob types describe arbitrarily-sized untyped binary data:

```grammar
type += (Blob size:<int>)
```

The `Addr` operation takes applies to locals instead of address offsets. Only
blob locals are allowed as `Addr` operands.

```grammar
rvalue -= (Addr (IntVal <int>))
rvalue += (Addr <local>)
```

Each continuation names the locals alive for the duration of it:

```grammar
continuation -= (Continuation (Params) stack:<int> <stmt>* <exit>)
              | (Subroutine (Params) stack:<int> <stmt>* <exit>)
              | (Except <local> stack:<int> <stmt>* <exit>)

continuation += (Continuation (Params) (Locals <local>*) <stmt>* <exit>)
              | (Subroutine (Params) (Locals <local>*) <stmt>* <exit>)
              | (Except <local> (Locals <local>*) <stmt>* <exit>)
```

*Rationale:* the lowering pass can focus stack allocation, without having to a
perform control-flow analysis for computing the set of alive locals for each
continuation.
