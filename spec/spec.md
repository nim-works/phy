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

The `proc(R, T0, ..., Tn)` type constructor constructs a type that is inhabited
by all procedure who take `T0` through `Tn` as parameters and return a value of
type `R`. The parameter type order is significant.

### Values, Objects, Locations, Cells, and Handles

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

A *handle* is the unique name of a location or cell. A *static handle* is
a name defined in the source code (e.g., the name of a variable), while a
*dynamic handle* is a *value* representing the name.

Handles can be *mutable* or *immutable*, which informs what operations are
possible on the l-value expression the handle is the root of.

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

Scopes can be nested. Except for the *top-level scope*, each scope has a
parent scope.

For the remainder of this document, `local_lookup(scope, name)` refers to
looking up the entity with name `name` in scope `scope`. Lookup fails when
there's no entity with `name` part of `scope`.

`lookup(scope, name)` means looking up an entity in `scope` and all its parent
scopes. `lookup(scope, name)` is equivalent to `local_lookup(scope, name)`,
and - if that fails and there is a parent scope - recursively performing
`lookup(parent(scope), name)`.

There is always a *current* scope.

*Opening a scope* means:
1. creating a new, empty scope, with the current scope as the parent
2. making the new scope the current scope

*Closing a scope* means replacing the current scope with its parent.

Unless explicitly noted otherwise, by default, an expression always opens a
new scope for itself and its sub-expressions.

### Expressions

At the moment, a few names are automatically part of a scope: `+`, `-`, `==`,
`<`, `<=`, `not`, `true`, and `false`.

#### Identifiers

```grammar
ident ::= (Ident name:<string>)
expr ::= <ident>
```

Refers to a previously declared entity.

Let `E` be the entity `lookup(S, name)` (where `S` is the current scope)
succeeds with. An error is reported if the lookup fails.

The meaning of the identifier depends on `E`:
* if `E` is a local variable, the expression is an l-value expression of the
  variable's type, evaluating to the location the local variable names
* if `E` is the built-in `true` or `false` value, the expression is an r-value
  expression of type `bool`
* if `E` is a procedure, the expression is an r-value expression of the
  procedure's type, evaluating to a procedural value representing the procedure

An error is reported if `E` is neither of the entities listed above.

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

The `cond` expression doesn't open a new scope for itself.

Let `A` be the type of `body` and `B` be type of `else` (which is `unit`, if
there's no `else`). An error is reported if:
* `cond` is a not a boolean expression, or
* `A` is not the same type as `B`, and `A` is not a subtype of `B` nor is `B` a
  subtype of `A`

The type of the `If` expression is the common type between `A` and `B`.

**Expression kind**: r-value
**Uses**: `cond`, `body`, and - if present - `else`

#### `While`

```grammar
expr += (While cond:<expr> body:<expr>)
```

Repeatedly evaluates `body`, as long as `cond` evaluates to `true`. Both
`body` and `cond` are part of a new scope.

Let `C` be the type of `cond` and let `T` be the type of `body`. An error is
reported if:
* `C` is not `bool`
* `T` is neither `unit` nor `void`

The type of a `While` expression depends on the `cond` expression. If `cond`
is the built-in `true` literal `(Ident "true")`, then the expression is of
type `void`, otherwise it is of type `unit`.

> TODO: once constant expression evaluation is specified, consider changing the
>       rules such that a `While` is of type `void` when the is a constant
>       expression that evaluates to true

**Expression kind**: r-value
**Uses**: `cond` and `body`

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
expr += (Call callee:<expr> args:<expr>*)
```

Applies the procedure `callee` evaluates to to the given arguments. An error is
reported if `callee` is not of `proc` type.

Let `proc(F0, ..., Fn) -> R` be the type of `callee`. Let `A0` through `Ax` be
the argument expressions (`args`). An error is reported if `n` is not equal to
`x`, or if the type of an argument expression is not equal to the corresponding
parameter's type.

> TODO: allow for argument subtype matches

The type of the expression is `R`.

Evaluation of the call happens as follows:
1. for each argument, going from left to right:
  1. a temporary location is created
  2. if the expression is an r-value expression, the resulting |object| is
     *moved* into the temporary; otherwise, the |object| stored in the location
     named by the l-value expression is *copied* into the temporary
  3. the location is bound to the parameter the argument is passed to
2. control is passed to the `callee` procedure
3. once control leaves the called procedure, the |object|s stored in the
   temporary locations are destroyed, in the reverse order they were assigned
   to

> TODO: once borrow checking is implemented, l-value arguments should always
>       be borrowed from when allowed by the borrow checker

When execution reaches the call expression, for each argument, the expression
is evaluated (including the side-effects) and the resulting value is bound to
the callee's corresponding parameter. Evaluation happens from *left to right*.

After evaluating the arguments (if any), control is passed to the callee.

> TODO: specification for the built-in operations is missing

**Expression kind**: r-value or `void`, depending on the return type
**Uses**: `callee` and each argument expression

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

Expressions appearing as an *immediate* sub-expression of the expression list
do not open a new scope for themselves.

**Expression kind**: same as that of the trailing expression
**Uses**: nothing

#### Logical `And`

```grammar
expr += (And a:<expr> b:<expr>)
```

Evaluates to `true` when both `a` and `b` evaluate to `true`, `false`
otherwise. `b` is only evaluated if `a` evaluates to `true`. The type of an
`And` expression is `bool`.

In terms of scoping, `(And a b)` is equivalent with `(If a b (Ident "false"))`.

An error is reported if the type of either `a` or `b` is not `bool`.

**Expression kind**: rvalue
**Uses**: `a` and `b`

#### Logical `Or`

```grammar
expr += (Or a:<expr> b:<expr>)
```

Evaluates to `true` when `a`, `b`, or both `a` and `b` evaluate to `true`,
`false` otherwise. `b` is only evaluated if `a` evaluates to `false`. The type
of an `Or` expression is `bool`.

In terms of scoping, `(Or a b)` is equivalent with `(If a (Ident "true") b)`.

An error is reported if the type of either `a` or `b` is not `bool`.

**Expression kind**: rvalue
**Uses**: `a` and `b`

#### Assignment

```grammar
expr += (Asgn lhs:<expr> rhs:<expr>)
```

Changes the |object| stored in the location identified by l-value expression
`lhs`. If the location already stores an |object|, the |object| is first
destroyed.

If `rhs` is an r-value expression, the assignment is a *move assignment*, and
the returned |object| is moved into the target location.

If the `rhs` is an l-value expression, the assignment is a *copy assignment*,
and a copy of the source |object| is created and moved into the target location.

> Future work: guarantee move assignments for l-value expressions in a select
> set of cases

Evaluation happens as follows:
1. the effects of `lhs` are computed, as well as the location `lhs` names
2. `rhs` is evaluated
3. if the assignment is a *copy assignment*: a copy of the `rhs` |object|
   is created
4. the |object| (if any) stored in the destination location is destroyed
5. the source |object| (or the copy thereof) is moved into the destination
   location

Let `A` be the type of `lhs` and `B` be the type of `rhs`. An error is reported
when:
* `lhs` is not a mutable l-value expression, or
* `B` is `void`, or
* `B` is not the same type as or a subtype of `A`

The type of an assignment is always `unit`.

**Expression kind**: r-value
**Uses**: the `rhs` expression

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

#### Procedure Type Constructors

```grammar
type_expr += (ProcTy ret:<type_expr> params:<type_expr>*)
```

Constructs the type `proc(ret, params[0], ..., params[n])`. An error is
reported if any of the provided *parameter* types is the `void` type.

### Declarations

#### Procedure

```grammar
decl ::= (ProcDecl name:<ident> ret:<type_expr> params:(Params <param_decl>*) body:<expr>)
```

Let `S` be the current scope. If `lookup(S, name)` succeeds, an error is
reported. Otherwise, `name` is added to `S`, referring to the declared
procedure. `name` is of type `proc(R)`, where `R` is the type `ret` evaluates
to.

A procedure declarations opens a new scope for the body and closes it
afterwards.

`body` must be of type `void`. It is the computation that is run when the
procedure is called.

`name` is added to `S` *before* any lookup takes place in the body.

##### Parameters

```grammar
param_decl ::= (ParamDecl name:<ident> type:<type_expr>)
```

Let `S` be the current scope. An error is reported if:
* `lookup(S, name)` succeeds
* `type` is `void`

`name` is added to the scope of the procedure body, referring to the handle of
the location the argument |object| is stored in. The handle is immutable.

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

#### Local Variable

```grammar
local_decl ::= (Decl name:<ident> expr:<expr>)
```

Declares a local variable, with the type inferred from `expr`, and assigns
`expr` to `name`. The assignment happens as-if performed by `(Asgn name expr)`.

Let `T` be the type of `expr`. An error is reported when:
* `T` is `void`, or
* `lookup(S, name)` (where `S` is the current scope) succeeds

`name` is added to the current scope *after* any lookup in `expr` happens.

```grammar
expr += <local_decl>
```

The declaration of a local can be used as an expression. Such expression is an
r-value expression of type `unit`.

### Modules

```grammar
module ::= (Module <decl>*)
top ::= <module>
```
