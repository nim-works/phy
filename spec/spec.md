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

The built-in types (also referred to as "primitive types") are:
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
expr += (IntVal <int>)
      | (FloatVal <float>)
```

The `IntVal` expression always has type `int`, `FloatVal` always type `float`.

#### `return`

```grammar
expr += (Return res:<expr>?)
```

Let `P` be the enclosing procedure of the `Return` expression. Let `T` be
the type of `res` -- if there's no `res` expression, `T` is `unit`. If `T`
doesn't match the return type of `P`, an error is reported.

The type of the `Return` expression is `void`. It returns control from the
current procedure to its caller.

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

#### Type Expression

```grammar
type_expr ::= (UnitTy)  # unit
           |  (BoolTy)  # bool
           |  (IntTy)   # int
           |  (FloatTy) # float
```

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
