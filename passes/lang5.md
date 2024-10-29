## L4 Language

```grammar
.extends lang3
```

```grammar
procdef -= (ProcDef <type_id> <int> (List <bblock>+))
procdef += (ProcDef <type_id> (List <type_id>*) (List <bblock>+))

loc_id ::= (Loc <int>)
```

Stack locations are listed with their type in the procedure header and are
addressed via have static names (`Loc`).

```grammar
stmt += (StorageLive <loc_id>+)
      | (StorageEnd <loc_id>+)
```

The start and end of their static livetimes is explicit. A `StorageLive` for a
stack location must dominate all `StorageEnd` operations for it. All stack
locations must one static livetime.

```grammar
bblock -= (Block  (Params <type_id>*) (Locals <type_id>*) <stmt>* <exit>)
        | (Except (Params <type_id>*) (Locals <type_id>*) <stmt>* <exit>)
bblock += (Block  (Params <type_id>*) (Locals <type_id>*) (List <loc_id>*) <stmt>* <exit>)
        | (Except (Params <type_id>*) (Locals <type_id>*) (List <loc_id>*) <stmt>* <exit>)
```

For convenience of the lowering pass, and because this information is
generally available already, every basic-block specifies which stack locations
are live at its entry, so that no inter-block data-flow analysis is necessary.

```grammar
rvalue += (Move <path>)
        | (Copy <path>)
        | (Move <loc_id>)
        | (Copy <loc_id>)
        | (Addr <loc_id>)

stmt += (Asgn <path> <value>)
      | (Asgn <loc_id> <value>)

path_elem += <loc_id>
```

Stack locations can be used as path roots, as well as the source for copy,
move, and address-of operations. Moving from a stack location does not affect
the live state of the location. Taking the address of a stack location yields
the dynamic memory address.
