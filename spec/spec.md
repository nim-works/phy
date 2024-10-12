## Phy Specification

This document describes the semantics of the source language.

A *program* consists of a single *module*. A *module* consists of zero or more
*declarations*.

A *declaration* introduces a new entity, one that can later be referred to with
the given name.

An *expression* is a term or a control-flow instruction. All expressions have a
*type*.

Expressions are further subdivided into:
* *l-value* expressions: an expression that refers to a location
* *r-value* expressions: an expression that produces a new value
* `void` expressions: control-flow instructions that don't produce a value

> TODO: reorder the definitions such that the term "locations" is defined
>       before it's used here

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

### Values, Objects, Locations, and Cells

A *value* is something that inhabits a type. An *aggregate value* is a value
inhabiting a composite type.

An *object* represents a *value*. If an object represents an aggregate value,
it has *sub-objects*. *Object*s are stored in *locations*, which can have
sub-locations storing the sub-objects, if any. A location not part of any
other location is called a *cell*.

Each object constructed at some point has a unique identity, even if it
represents the same value as another object. An object can only be stored in
a single location at a time (which is referred to as its *owner*), but can
move locations (thereby changing the owner).

Changing the object stored in a sub-location also modifies the object of the
parent location, but without changing its *identity*.

> Note: the term "object" is intended as a placeholder until a better,
> less overloaded term is found.

> Note: "constructing a value" is sometimes used interchangeably with
> "constructing an object"

### Normal, Linear, and Affine Types

How an object representing a value inhabiting a type is allowed to be used
depends on whether the type is a normal, linear, or affine type:

| Type   | No Use | Single Use | Multi Use |
| ------ | ------ | ---------- | --------- |
| Normal | Yes    | Yes        | Yes       |
| Affine | Yes    | Yes        | No        |
| Linear | No     | Yes        | No        |

What constitutes a *use* of an object is described in this document.

Using an r-value expression means using the object it produces. Using an l-
value expression means using the object stored in the named location.

> note: at the moment, all types are *normal* types

### Lookup

*Entities* are part of *scopes*. They're queried from their scope via their
name. This is referred to as *looking up the entity* (or just *lookup* ).

For the remainder of this document, `lookup(scope, name)` refers to looking up
the entity with name `name` in scope `scope`. Lookup fails when there's no
entity with `name` part of `scope`.

### Expressions

At the moment, a few names are automatically part of a scope: `+`, `-`, `==`,
`<`, `<=`, `not`, `true`, and `false`.

#### Identifiers

```grammar
ident ::= (Ident name:<string>)
expr ::= <ident>
```

If `name` is "true" or "false", the expression is of type `bool` and refers to
the `true` or `false` value, respectively.

Otherwise, an error is reported.

**Expression kind**: r-value
**Uses**: nothing

#### Literals

```grammar
int_val ::= (IntVal <int>)
expr += <int_val>
      | (FloatVal <float>)
```

The `IntVal` expression always has type `int`, `FloatVal` always type `float`.

**Expression kind**: r-value
**Uses**: nothing

#### `If`

```grammar
expr += (If cond:<expr> body:<expr> else:<expr>?)
```

`If` is a control-flow expression, which requires a boolean expression in the
`cond` position. If the `cond` expression evaluates to `true`, it will execute
the `body` expression, otherwise the `else` expression -- if there's no `else`
expression, it is assumed to be `unit`.

Let `A` be the type of `body` and `B` be type of `else` (which is `unit`, if
there's no `else`). An error is reported if:
* `cond` is a not a boolean expression, or
* `A` is not the same type as `B`, and `A` is not a subtype of `B` nor is `B` a
  subtype of `A` 

The type of the `If` expression is the common type between `A` and `B`.

**Expression kind**: r-value
**Uses**: `cond`, `body`, and - if present - `else`

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

**Expression kind**: `void`
**Uses**: `expr`, if present

#### `Unreachable`

```grammar
expr += (Unreachable)
```

Marks a control-flow path as unreachable. In case program execution does reach
the `Unreachable` expression, the program immediately terminates. A compiler
*may* report an error if it can statically detect that control-flow can reach
an `Unreachable` expression within a procedure.

The type of the `Unreachable` expression is `void`.

**Expression kind**: `void`
**Uses**: nothing

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

**Expression kind**: r-value or `void`, depending on the return type
**Uses**: each argument expression

#### Tuple Constructors

```grammar
expr += (TupleCons)
```

Constructs a value of type `unit`.

```grammar
expr += (TupleCons <expr>+)
```

Constructs a value of type `tuple(T0..Tn)`, where `T0` is the type of the first
expression, `T1` the type of the second expression (if any), and so on.

An error is reported if any `Tx` is `void`.

**Expression kind**: r-value
**Uses**: each operand expression

#### Tuple Elimination

```grammar
expr += (FieldAccess tup:<expr> index:<int_val>)
```

Retrieves the value from the `index`-th position of the tuple.

Let `T` be the type of `tup`. If `T` is not a `tuple` type, an error is
reported. If `index` is an integer value less than 0, or greater than or equal
to the number of positions in the tuple type `T`, an error is reported.

Given type `tuple(T[0], .., T[n])` for `T`, the type of the expression is
`T[index]`.

**Expression kind**: same as `tup`
**Uses**: nothing

#### Expression Lists

```grammar
expr += (Exprs <expr>+)
```

A non-empty list of expressions, where the tail expression may be any type and
preceding ones must be `unit` or `void`. An error is reported if a non-tail
expression is any type outside of `unit` or `void`.

The type of the expression list is inferred as `void` if any non-trailing
expression is `void`, otherwise the type is that of the trailing expression.

**Expression kind**: same as that of the trailing expression
**Uses**: nothing

### Type Expressions

```grammar
type_expr ::= (VoidTy)  # void
           |  (UnitTy)  # unit
           |  (BoolTy)  # bool
           |  (IntTy)   # int
           |  (FloatTy) # float
```

#### Type Lookup

```grammar
type_expr += (Ident name:<string>)
```

Let `S` be the current scope. If `lookup(S, name)` fails or doesn't yield a
type, an error is reported. Otherwise, the identifier refers to the type that
that was bound to the identifier earlier.

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

#### Type Alias

```grammar
decl += (TypeDecl name:<ident> typ:<type_expr>)
```

Let `S` be the current scope. If `lookup(S, name)` succeeds, an error is
reported. If not, `name` is added to `S`, referring to the type `typ` evaluates
to.

Type aliases only give a name to a type, for more convenient usage thereof --
they do not alter or affect the type in any way. The evaluated type is *bound*
to the name, meaning that replacing the identifier with the provided expression
verbatim does *not* necessarily yield a program with the same meaning.

`name` is added to `S` after any lookup takes place in `typ`.

### Modules

```grammar
module ::= (Module <decl>*)
top ::= <module>
```
