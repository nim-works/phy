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
succeeds with. An error is reported when:
* the lookup fails, or
* `E` is neither a local variable nor the built-in `true` or `false`

If `E` is a local variable, the type of the expression is that of the local
variable. If `E` is the built-in `true` or `false` entity, the type is `bool`.

**Expression kind**: r-value for boolean literals, otherwise l-value
**Uses**: nothing

#### Literals

```grammar
int_val ::= (IntVal <int>)
expr += <int_val>
      | (FloatVal <float>)
```

The `IntVal` expression always has type `int`, `FloatVal` always type `float`.

#### `If`

```grammar
expr += (If cond:<expr> body:<expr> else:<expr>?)
```

`If` is a control-flow expression, which requires a boolean expression in the
`cond` position. If the `cond` expression evaluates to `true`, it will execute
the `body` expression, otherwise the `else` expression -- if there's no `else`
expression, it is assumed to be `unit`.

For both `body` and `else`, a new scope is opened for the expressions and
closed afterwards.

Let `A` be the type of `body` and `B` be type of `else` (which is `unit`, if
there's no `else`). An error is reported if:
* `cond` is a not a boolean expression, or
* `A` is not the same type as `B`, and `A` is not a subtype of `B` nor is `B` a
  subtype of `A` 

The type of the `If` expression is the common type between `A` and `B`.

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

#### Expression Lists

```grammar
expr += (Exprs <expr>+)
```

A non-empty list of expressions, where the tail expression may be any type and
preceding ones must be `unit` or `void`. An error is reported if a non-tail
expression is any type outside of `unit` or `void`.

The type of the expression list is inferred as `void` if any non-trailing
expression is `void`, otherwise the type is that of the trailing expression.

**Expression kind**: same as the trailing expression
**Uses**: nothing

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
* `lhs` is not an l-value expression, or
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

### Declarations

#### Procedure

```grammar
decl ::= (ProcDecl name:<ident> ret:<type_expr> params:(Params) body:<expr>)
```

Let `S` be the current scope. If `lookup(S, name)` succeeds, an error is
reported. Otherwise, `name` is added to `S`, referring to the declared
procedure.

A procedure declarations opens a new scope for the body and closes it
afterwards.

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
