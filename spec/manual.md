This document provides an overview of the current meta-language. It's a work-
in-progress and not intended as an exhaustive description of the language.

The meta-language is a functional language with some declarative extensions,
with a focus on defining/describing the semantics of programming languages.

## Types

There are three built-in primitive types:
* `z` - integer numbers
* `r` - rational numbers
* `bool` - `true` and `false`

There are some additional primitive types, such as `void` and `all`, but
they're not available for use directly.

Tuple, function, list (introduced with `*` prefix), and sum types (introduced
with `+` infix) are also supported. Tuples are constructed with the `(1, 2)`
syntax; the other types have no dedicated terms inhabiting them, only
identifiers to whom a value of the respective type was bound.

Except for type constructors, all non-pattern expressions have a type.

### Custom Data Types

Custom data types are introduced via the `typ` declaration:
```nim
typ MyList:
  Nil
  Cons(z, MyList)
```

`Nil` introduces, if not present already, a nominal unit type, which is
inhabited by the single term `Nil`.

`Cons` is a *constructor*; `Cons(z, MyList)` is a *pattern type*, inhabited by
all terms matching the pattern (e.g., `Cons(1, Nil)`, `Cons(2, Nil)`,
`Cons(3, Cons(1, Nil)))`, etc.). A *pattern type* appearing within a `typ`
declaration automatically introduces, if not present already, the given
constructor and pattern type.

`MyList` is the sum between `Nil` and `Cons(z, MyList)`. There must be no
overlap between the summands -- the set of terms inhabiting a summand must
be disjoint from those inhabiting other summands.

`subtype` is similar to the `typ` declaration, with the addition that it
verifies that the defined type is a subtype of the specified base type. An
abstract data type `A` is the subtype of another abstract data type `B` if
all constructions of `A` are also constructions of `B`.

## Functions

Functions are defined via the `function` declaration:
```nim
function map, z -> z:
  ...
```

The first argument is the function's name, the second argument the type (which
must be a function type).

Functions are not required to be total: the `fail` expression marks some input
as "unmapped" (i.e., not part of the function's domain).

### Function Bodies

Function bodies can use expressions and statements not available elsewhere.

#### Case

```nim
function map, z -> z:
  case _
  of 1: 2
  of 2: 3
  of 3: fail
  of z_1: z_1 + 1
```

The `case` expression is used for pattern matching. The labels in the `of`
branches are pattern expressions, with each branch being in its own scope.

`of` branches are tried top to bottom. If none matches for the given value, the
function fails.

Top-level `case` expressions may use `_` as the operand to use the function's
input as the argument.

#### If

```nim
if a == 1:
  2
else:
  3
```

Evaluates either the first or second branch, depending on whether the condition
evaluates to true or false. A missing `else` branch is treated like
`else: fail`.

#### Let

```nim
let z_1 = 10
```

`let` statements may appear before `let` statements and `if` or `case`
expressions. They introduce named bindings that exists for the duration of
the surrounding scope.

## Relations

Relations are inductively-defined relations between values.

Example:
```nim
relation length(inp MyList, out z):
  axiom "empty", Nil, 0
  rule "non-empty":
    premise rel(MyList_1, z_1)
    conclusion Cons(z, MyList_1), 1 + z_1
```

Relation parameters must be marked as either inputs or outputs, which affects
how the relation may be used. A relation with output parameters must only be
used in the `premise` statement of a `rule` -- relations with no output
parameter may be used like normal functions.

`axiom name, a, b` is a short-hand for `rule name: conclusion a, b`, meant for
unconstrained rules that always hold for their values.

The `premise` statement specifies a relation that must hold true for the rule
to apply. Expressions appearing in the invocation's input positions must be
value expressions, the others must be patterns.

The `where pat, term` statement specifies a pattern that must match what the
term on the right evaluates to for the rule to apply. When `pat` is a single
identifier pattern, it can also be written as `let pat = term`.

The `condition` statement specifies a boolean term that must evaluate to `true`
for the rule to apply.

The `conclusion` must come last and appear exactly one time. It defines how the
parameters the rule covers look like. Expressions in input positions must be
*patterns*, expressions in output positions must be value expressions.

## Patterns

Patterns are made up of constructions, type names, and binders. They also
support matching of repetitions via `*x` (zero or more) and `+x` (one or more)
within data type constructions.

### Bindings

Within a pattern context, suffixing the name of a type with a `_x` (where `x`
can be any number of identifier not including an underscore) introduces a
named binding.
