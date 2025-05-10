## L6 Language

```grammar
.extends lang5
```

It's now possible to define global *variables*, which are locations that can be
assigned to, read from, and have their address taken.

Non-variables continue to works as they did previously.

```grammar
globalInit -= <dataInit>
globaldef += (GlobalLoc <type> <dataInit>)

dataInit -= (Data <int> <int>)
          | (Data <int> (StringVal <string>))
dataInit += (Data <type>)
          | (Data <type> (StringVal <string>))
```

> TODO: instead of there being a `GlobalLoc`, `GlobalDef` should change its
>       meaning to be that `GlobalLoc` from the L6 onwards. However, this is
>       currently not possible, as some IL producers (mis-)use the globals for
>       passing constants with external meaning to the VM

They may be used as a `Copy` source and in paths, much like locals.
```grammar
global ::= (Global <int>)

stmt += (Asgn <global> <expr>)

expr += (Addr <global>)
path_elem += <global>
```
