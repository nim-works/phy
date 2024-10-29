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
path ::= (At    <path> elem:<value>)
      |  (Field <path> field:<int>)
      |  <loc_id>

rvalue += (Addr <path>)
        | (Move <path>)
        | (Copy <path>)

stmt += (Asgn <path> <value>)
```

Path expressions with a `Loc` as the root can be used as the operand for copy,
move, and address-of operations. Moving from a stack location does not affect
the liveness of the location. Taking the address of a stack location yields
its dynamic memory address.
