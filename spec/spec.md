## Phy Specification

This document describes the semantics of the source language.

A *program* consists of a single *module*. A *module* consists of zero or more
*declarations*.

A *declaration* introduces a new entity, one that can later be referred to with
the given name.

An *expression* is a term or a control-flow instruction. All expressions have a
*type*.

A *statement* is a computation without a type.

> Note: at the moment, the grammar describes the grammar of the parse-tree,
> not the grammar of the textual representation (i.e., how the parse-tree is
> constructed from tokens).

### Types

The primitive types are:
* `void`
* `unit`
* `bool`
* `int`
* `float`

`void` is the *empty type*, and functions as the *bottom type*. It is
uninhabited, meaning that there are no valid terms for it.

`unit` is a type that has only *one* value.

`bool` is a type that has two values: `true` and `false`.

`int` is the type of signed integer values, where the size and range is target-
dependent.

`float` is the type of floating point values, where the size is target-
dependent.

#### Composite Types

Types can be combined into *composite types*.

The `tuple(T1, ..., Tn)` type constructor constructs a *product type* (i.e., a
type that is the product of the `T1`..`Tn` types). The operand order is
significant, meaning that `tuple(int, float)` does not construct the same type
as `tuple(float, int)`.

`tuple()` (i.e., the product of no types) is a special case, and is equal to
the `unit` type.

The `union(T0, ..., Tn)` type constructor constructs a *sum type* (i.e., a type
that is the sum of the `T0` .. `Tn` types). The operand order is *not*
significant, meaning that `union(int, float)` and `union(float, int)` construct
the same type.

`union(...)` is the supertype of all its operand types.

### Lookup

*Entities* are part of *scopes*. They're queried from their scope via their
name. This is referred to as *looking up the entity* (or just *lookup* ).

For the remainder of this document, `lookup(scope, name)` refers to looking up
the entity with name `name` in scope `scope`. Lookup fails when there's no
entity with `name` part of `scope`.

### Expressions

At the moment, a few names are automatically part of a scope: `+`, `-`, `==`,
`<`, `<=`, `not`.

#### Identifiers

```grammar
ident ::= (Ident name:<string>)
expr ::= <ident>
```

If `name` is "true" or "false", the expression is of type `bool` and refers to
the `true` or `false` value, respectively.

Otherwise, an error is reported.

#### Literals

```grammar
int_val ::= (IntVal <int>)
expr += <int_val>
      | (FloatVal <float>)
```

The `IntVal` expression always has type `int`, `FloatVal` always type `float`.

#### `Return`

```grammar
expr += (Return res:<expr>?)
```

Let `P` be the enclosing procedure of the `Return` expression. Let `T` be
the type of `res` -- if there's no `res` expression, `T` is `unit`. An error
is reported if:
* `T` is not the same type as the return type of `P`, or a *subtype* thereof
* `T` is `void`

The type of the `Return` expression is `void`. It returns control from the
current procedure to its caller.

#### `Unreachable`

```grammar
expr += (Unreachable)
```

Marks a control-flow path as unreachable. In case program execution does reach
the `Unreachable` expression, the program immediately terminates. A compiler
*may* report an error if it can statically detect that control-flow can reach
an `Unreachable` expression within a procedure.

The type of the `Unreachable` expression is `void`.

#### Calls

```grammar
expr += (Call callee:<ident> args:<expr>*)
```

Let `S` be the current *scope*. If `lookup(S, callee)` fails, an error is
reported.

Let `C` be the result of `lookup(S, callee)`. If `C` is not a procedure, an
error is reported.

Let `A0`..`Ax` be the types of the argument expressions. Let `F0`..`Fy` be
the types of the parameters of `C`. If `x` is not equal to `y`, an error is
reported. Each argument type must match (i.e., be equal to) that of the
corresponding parameter. If that's not the case, an error is reported.

The type of the call is the *return type* of `C`.

When execution reaches the call expression, for each argument, the expression
is evaluated (including the side-effects) and the resulting value is bound to
the callee's corresponding parameter. Evaluation happens from *left to right*.

After evaluating the arguments (if any), control is passed to the callee.

> TODO: specification for the built-in operations is missing

#### Tuple Constructors

```grammar
expr += (TupleCons)         # first form
      | (TupleCons <expr>+) # second form
```

The first form constructs a value of type `unit`.

The second form construct a value of type `tuple(T1..Tn)`, where `T1` is the
type of the first expression, `T2` the type of the second expression (if any),
and so on.

An error is reported if any `Tx` is `void`.

### Tuple Elimination

```grammar
expr += (FieldAccess tup:<expr> index:<int_val>)
```

Retrieves the value from the `index`-th position of the tuple.

Let `T` be the type of `tup`. If `T` is not a `tuple` type, an error is
reported. If `index` is an integer value less than 0, or greater than or equal
to the number of positions in the tuple type `T`, an error is reported.

Given type `tuple(T[0], .., T[n])` for `T`, the type of the expression is
`T[index]`.

### Type Expressions

```grammar
type_expr ::= (VoidTy)  # void
           |  (UnitTy)  # unit
           |  (BoolTy)  # bool
           |  (IntTy)   # int
           |  (FloatTy) # float
```

#### Tuple Type Constructors

```grammar
type_expr += (TupleTy)              # first form
          |  (TupleTy <type_expr>+) # second form
```

The first form of the `TupleTy` operator produces the `unit` type.

> TODO: this behaviour makes sense, but it renders `UnitTy` redundant. Consider
> removing the latter, or at least making it an alias for `(TupleTy)`.

The second form constructs a `tuple` type from the given types. Allowed
operand type kinds are: `unit`, `int`, `float`, `tuple`, and `union`. An error
is reported for any other type.

#### Union Type Constructors

```grammar
type_expr += (UnionTy <type_expr>+)
```

`UnionTy` constructs a `union` type from the given types.

An error is reported if:
* any operand is the `void` type
* a type is provided more than once

### Declarations

#### Procedure

```grammar
decl ::= (ProcDecl name:<ident> ret:<type_expr> params:(Params) body:<expr>)
```

Let `S` be the current scope. If `lookup(S, name)` succeeds, an error is
reported. Otherwise, `name` is added to `S`, referring to the declared
procedure.

`body` must be of type `void`. It is the computation that is run when the
procedure is called.

`name` is added to `S` *before* any lookup takes place in the body.

### Modules

```grammar
module ::= (Module <decl>*)
top ::= <module>
```
