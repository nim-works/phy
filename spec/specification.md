## Phy Specification

This document provides the *formal definition* of the source language's syntax
and semantics. It's the authoritative source on both.

Both the source language and the specification are a **work-in-progress**.

> Note: the goal is to provide the definition in the form a NimSkull macro-
> based DSL, from which this document is then generated.

> Note: the use of mathematical notation throughout the document is not fully
> fleshed out yet. Not using any form of typesetting also doesn't help.

### Abstract Syntax

This section specifies the *abstract syntax* (not the *concrete syntax*) of
the source language, using S-expressions to represent trees.

> Note: no dedicated concrete syntax exists at this time

`<string>`, `<int>`, and `<float>` refer to S-expression strings, integer
numbers, and decimal numbers, respectively.

```grammar
ident    ::= (Ident <string>)
intVal   ::= (IntVal <int>)
floatVal ::= (FloatVal <float>)
expr     ::= <ident>
          |  <intVal>
          |  <floatVal>
          |  (TupleCons <expr>*)
          |  (Call <expr>+)
          |  (FieldAccess <expr> <intVal>)
          |  (And <expr> <expr>)
          |  (Or <expr> <expr>)
          |  (If <expr> <expr> <expr>?)
          |  (While <expr> <expr>)
          |  (Return <expr>?)
          |  (Unreachable)
          |  (Exprs <expr>+)
          |  (Asgn <expr> <expr>)
          |  (Decl <ident> <expr>)
texpr    ::= <ident>
          |  (VoidTy)
          |  (UnitTy)
          |  (BoolTy)
          |  (IntTy)
          |  (FloatTy)
          |  (TupleTy <texpr>*)
          |  (UnionTy <texpr>+)
          |  (ProcTy <texpr>+)

param_decl ::= (ParamDecl name:<ident> type:<texpr>)
decl       ::= (ProcDecl <ident> <texpr> (ParamDecl <param_decl>) <expr>)
            |  (TypeDecl <ident> <texpr>)  # type alias
module     ::= (Module <decl>*)

top        ::= <module> # `module` is the entry symbol
```

### Desugaring

Some of the expressions in the abstract syntax specified above are
*syntactic sugar* for which there exists a function to a desugared form.

```
(And e_1 e_2) <--> (If e_1 e_2 (Ident "false")) # D-and
(Or e_1 e_2)  <--> (If e_1 (Ident "true") e_2)  # D-or

(Decl x e_1) <--> (Let x e_1 (TupleCons)) # D-single-decl
(Exprs e_1* (Decl x e_2) e_3+) <--> (Exprs e_1* (Let x e_2 (Exprs e_3+))) # D-decl-in-exprs

(If e_1 e_2) <--> (If e_1 e_2 (TupleCons)) # D-single-branch-if

(If (Exprs e_1* e_2) e_3 e_4) <--> (Exprs e_1* (If e_2 e_3 e_4)) # D-unwrap-if
```

> TODO: it's not explained what `_1`, `*`, `+` mean

In the remainder of this document, all references to abstract syntax refer to
the desugared form (the *language core*).

### Semantic Grammar

```
c   ::= n                           # corresponds to `(IntVal n)`
     |  rational                    # corresponds to `(FloatVal rational)`
     |  true                        # corresponds to `(Ident "true")`
     |  false                       # corresponds to `(Ident "false")`
     |  (TupleCons)                 # unit value
     |  (Unreachable)               # an irrecoverable error
l   ::= ...                         # first-class location
val ::= <c>
     |  <l>
     |  (TupleCons <val>+)          # tuple value
     |  (proc <typ> [x <typ>]* <e>) # procedural value
typ ::= void                        # corresponds to `(VoidTy)`
     |  unit                        # corresponds to `(UnitTy)`
     |  bool                        # corresponds to `(BoolTy)`
     |  int                         # corresponds to `(IntTy)`
     |  float                       # corresponds to `(FloatTy)`
     |  (mut <typ>)
     |  (type <typ>)
     |  (TupleTy <typ>+)
     |  (UnionTy <typ>+)
     |  (ProcTy  <typ>+)
le  ::= x                   # | subset of expressions where all non-lvalue
     |  (FieldAccess le n)  # | operands were already evaluated
e   ::= x | val | typ | ... # includes all expressions from the abstract syntax

e += (Frame typ e) # a special expression for assisting with evaluation
```

### Static Semantics

#### Notation and Concepts

Typing judgments are of the form:
```
C |- expr : typ
```
which is read as: "within context C, it holds that `expr` is of type `typ`".

The typing rules are given as *deduction rules* of the following form:
```
premise_1   premise_2
---------------------
     conclusion
```
which is read as: "if `premise_1` and `premise_2` hold true, it follows that
`conclusion` also holds true".

A deduction rule without a premise is called an *axiom*; the conclusion always
holds true.

#### Type Relations

All type equality uses *structural equality*. The order of types in a `TupleTy`
and `ProcTy` is significant, in `UnionTy` it is not. Formally:
```
void  = void
unit  = unit
bool  = bool
int   = int
float = float

(TupleTy a_0 ... a_n) = (TupleTy b_0 ... b_n)  (where a_0 = b_0 ... a_n = b_n ^ n >= 1)
(ProcTy  a_0 ... a_n) = (ProcTy  b_0 ... b_n)  (where a_0 = b_0 ... a_n = b_n)
(UnionTy a_0 ... a_n) = (UnionTy b_0 ... b_n)  (where {a_0 ... a_n} = {b_0 ... b_0})
```

`a <: b` means "a is a subtype of b". `a <:= b` means "a is a subtype of or
equal to b".
```
# void is the bottom type; it's a subtype of all other types
void <: unit
void <: bool
void <: int
void <: float
void <: (TupleTy typ+)
void <: (UnionTy typ+)
void <: (ProcTy typ+)

typ_1 <: (UnionTy typ_1 typ_2 ...) # | a type is a subtype of `UnionTy` if it's
                                   # | a part of the union (in any position)
```

#### Typing Judgments

This section describes how types are assigned to the abstract syntax. An
abstract syntax tree is well-formed if and only if a type can be assigned to
it.

`C` (the context) is a record with the following abstract syntax:
```
C ::= { symbols S
        return typ }
```

`S` is the function mapping identifiers to types. `return` is the return type
of the procedure being judged.

Unless explicitly stated otherwise, a deduction rule's conclusion is always
a single *typing judgement*, whereas a premise may be either a
*typing judgment* or *side condition*.

##### Primitive Types

```

-------------------------- # S-void-type
C |- (VoidTy): (type void)


-------------------------- # S-unit-type
C |- (UnitTy): (type unit)


-------------------------- # S-bool-type
C |- (BoolTy): (type bool)


------------------------ # S-int-type
C |- (IntTy): (type int)


---------------------------- # S-float-type
C |- (FloatTy): (type float)


----------------------------- # S-empty-tuple-type
C |- (TupleTy) |- (type unit)
```

##### Identifiers

```
x in C   C.symbols(x) = typ
--------------------------- # S-identifier
C |- x : typ
```

##### Composite Types

```
C |- e : (type typ) ...  typ != void ...
--------------------------------------------- # S-tuple-type
C |- (TupleTy e+) |- (type (TupleTy typ ...))

C |- e : (type typ) ...  typ != void ...  |{typ ...}| = |e| # each type must be unique
----------------------------------------------------------- # S-union-type
C |- (UnionTy e+) |- (type (UnionTy typ ...))

C |- res : (type typ_1)   C |- e : (type typ_2) ...  typ_2 != void ...
---------------------------------------------------------------------- # S-proc-type
C |- (ProcTy res e*) : (type (ProcTy typ_1 typ_2 ...))
```

##### Expressions

Mutability is part of the type system. `All[typ]` means "matches `(mut typ)`
and `typ`", which makes it writing deduction rules applicable to expression of
both mutable and immutable type easier.

`built_ins` is a set of names: `{==, <=, <, +, -, true, false}`.

```

------------ # S-integer-numbers
C |- n : int


--------------------- # S-rational-numbers
C |- rational : float


---------------- # S-false
C |- false: bool


---------------- # S-true
C |- true : bool


----------------------- # S-unit
C |- (TupleCons) : unit


------------------------- # S-unreachable
C |- (Unreachable) : void

C |- e : All[typ] ...  typ != void ...
--------------------------------------- # S-tuple
C |- (TupleCons e+) : (TupleTy typ ...)

C |- e : All[typ]   C.return <:= typ
------------------------------------ # S-return
C |- (Return e) : void

C.return = unit
-------------------- # S-return-unit
C |- (Return) : void

C |- e: typ_1  typ_1 = (TupleTy ...)  typ_2 = typ_1 at n
-------------------------------------------------------- # S-field
C |- (FieldAccess e n) : typ_2

C |- e: (mut typ_1)  typ_1 = (TupleTy ...)  typ_1 at n = typ_2
-------------------------------------------------------------- # S-mut-field
C |- (FieldAccess e n) : (mut typ_2)

C |- e_1 : (mut typ_1)  C |- e_2 : All[typ_2]  typ_2 <:= typ_1
-------------------------------------------------------------- # S-asgn
C |- (Asgn e_1 e_2)

x notin C.symbols  x notin built_ins  C |- e_1 : All[typ_1]  C + symbols with x -> (mut typ_1) |- e_2 : All[typ_2]
------------------------------------------------------------------------------------------------------------------ # S-let
C |- (Let x e_1 e_2) : typ_2

C |- e_1 : All[typ_1] ...  typ_1 = unit ...  C |- e_2 : typ_2
------------------------------------------------------------- # S-exprs
C |- (Exprs e_1* e_2) : typ_2

C |- e_1 : All[typ_1] ...  typ_1 = unit ...  C |- e_3 : All[typ_3] ...  typ_3 = unit ...  C |- e_2 : typ_2  typ_2 = void  C |- e_4 : typ_4
------------------------------------------------------------------------------------------------------------------------------------------ # S-void-short-circuit
C |- (Exprs e_1* e_2 e_3* e_4) : void

C |- e_1 : All[bool]  C |- e_2 : All[typ_1]  C |- e_3 : All[typ_2]
------------------------------------------------------------------ # S-if
C |- (If e_1 e_2 e_3) : typ_1 v typ_2   # least upper bound

C |- e_1 : All[bool]  C |- e_2 : typ  typ in {void, unit}
--------------------------------------------------------- # S-while
C |- (While e_1 e_2) : unit

C |- e : All[typ]  typ in {unit, void}
-------------------------------------- # S-while-true
C |- (While true e) : void

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ in {int, float}
----------------------------------------------------------------- # S-builtin-plus
C |- (Call + e_1 e_2) : typ_1

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ in {int, float}
----------------------------------------------------------------- # S-builtin-minus
C |- (Call - e_1 e_2) : typ_1

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ in {int, float, bool}
----------------------------------------------------------------------- # S-builtin-eq
C |- (Call == e_1 e_2) : typ_1

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ in {int, float}
----------------------------------------------------------------- # S-builtin-le
C |- (Call <= e_1 e_2) : bool

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ in {int, float}
----------------------------------------------------------------- # S-builtin-lt
C |- (Call < e_1 e_2) : bool

C |- e_1 : All[typ_1]  typ_1 = (ProcTy typ_r typ_p*)  C |- e_2 : All[typ_a] ...  typ_a <:= typ_p ...
---------------------------------------------------------------------------------------------------- # S-call
C |- (Call e_1 e_2*) : typ_r
```

##### Extras

Typing judgments for abstract syntax trees not representable with the source
language. They still need to be typed, in order to be able to prove type
preservation for the later operational semantics.

```
C |- e : typ_2  typ_2 <:= typ_1
------------------------------- # S-Frame
(Frame typ_1 e) : typ_1


--------------------------------------------------------- # S-proc-val
C |- (proc typ_r [x typ_p]^ e) : (ProcTy typ_r typ_p ...)
```

##### Modules and Declarations

Top-level declarations use slightly different judgments, of the form:
```
C_1 |- e --> C_2
```
which is read as "under context `C_1`, `e` *steps to* context `C_2`".

```
C |- e : (type typ)
-------------------------------------------------------- # S-type-decl
C |- (TypeDecl x e) --> C + symbols with x -> (type typ)

x_1 notin C.symbols  C |- e_1 : (type typ_1)  C |- e_2 : (type typ_2) ...  typ_2 != void ...
p = (ProcTy typ_1 typ_2 ...)  C + return = typ + symbols with x_1 -> p, x_2 -> typ_2 ... |- e : void
---------------------------------------------------------------------------------------------------- # S-proc-decl
C |- (ProcDecl x_1 e_1 (Params (ParamDecl x_2 e_2)*) e_3) --> C + symbols with x_1 -> p


--------------------
C |- (Module) --> C

C_n |- decl --> C_n+1 ...
------------------------------- # S-module
C_1 |- (Module decl+) --> C_n+1
```

A module is well-formed if it's either empty or all declarations within are
well-formed.

> TODO: the concept of an "entry procedure" is missing

### Dynamic Semantics

This section describes how expressions are evaluated, using small-step
operational semantics with evaluation contexts (also known as *reduction semantics*
or *context semantics*).

#### Notation and Concepts

Small-step operational semantics describe operation of a program as a series
of *small steps* (hence the name).

```
configuration_1 --> configuration_2
```
is read as: "`configuration_1` *steps to* `configuration_2`".

```
premise_1  premise_2
--------------------
      a --> b
```
is read as: "if `premise_1` and `premise_2` hold true, it follows that `a`
steps to `b`".

A *notion of reduction* describes how a *redex* (reduction expression)
reduces to a term. They're written as:
```
redex  ~~>  term
```
which is read as: "`redex` reduces to `term`".

An *evaluation context* (usually named `E`) specifies where reduction may take
place, and thus the *order of evaluation*. It represents an expression with
a *hole* in it, with the hole denoted by `[]`. The *plug function*
`E[t_1] = t_2` fills the hole of `E` with `t_1` yielding a new term `t_2`.

Stepping is combined with the notions of reduction through an evaluation
context:
```
   t_1 ~~> t_2
-----------------
E[t_1] --> E[t_2]
```
which is read as: "If `t_1` reduces to `t_2`, then `t_1` plugged into `E`
steps to `t_2` plugged into `E`".

#### Evaluation

The configuration for steps is a tuple of the form `C; e`, where `C` is the
*context* record. It's abstract syntax is as follows:
```
C ::= { locs S }
```

`locs` is a store (`S`), which maps *locations* to *values* (`S(l) = val`).
Mutable state is modeled via locations.

`e[x/y]` means "`e` with all occurrences of name `x` replaced with `y`".

It is assumed that all identifiers referring to procedures were replaced with
`(proc r [x p]* body)` prior to evaluation, where `x` and `typ` are the names
and types of the procedure's parameters, `r` is the procedure's return type,
and `body` is the procedure's body.

> TODO: the assumption above should be baked into the static semantics
>       somehow...

> TODO: the static semantics also needs to describe how a `(Module ...)` is
>       reduced to a `(proc ...)` value, which is what a program is, in the
>       end -- a procedural value

The evaluation contexts are (evaluation happens left to right):

```
E' ::= []
    |  (FieldExpr E' n)

E  ::= []
    |  (Exprs E e*)
    |  (FieldAccess E n)
    |  (Asgn E' n)
    |  (Asgn le E)
    |  (Asgn E v)
    |  (TupleCons val* E e*)
    |  (Call val* E e*)
    |  (Call x val* E e*)
    |  (If E e e)
    |  (Let x E e)
    |  (Return E)

B  ::= []
    |  E[B]
    |  (Frame typ B)
```

The pure notions of reduction are:
```
(Exprs val)             ~~>  val        # E-exprs-fold
(Exprs (TupleCons) e+)  ~~>  (Exprs e+) # E-exprs
(If true e_1 e_2)       ~~>  e_1        # E-if-true
(If false e_1 e_2)      ~~>  e_2        # E-if-false

(While e_1 e_2)  ~~>  (If e_1 (Exprs e_2 (While e_1 e_2)) (TupleCons)) # E-while

(FieldAccess (TupleCons val^n) i)  ~~>  val_i # E-field-access

val_3 = int_add(val_1, val_2)  val_3 != {}
------------------------------------------ # E-add-int
(Call + val_1 val_2)  ~~>  val_3

int_add(val_1, val_2) = {}
---------------------------------------- # E-add-int-overflow
(Call + val_1 val_2)  ~~>  (Unreachable)

val_3 = int_add(val_1, val_2)  val_3 != {}
------------------------------------------ # E-sub-int
(Call - val_1 val_2)  ~~>  val_3

int_sub(val_1, val_2) = {}
---------------------------------------- # E-sub-int-overflow
(Call - val_1 val_2)  ~~>  (Unreachable)

val_3 = float_add(val_1, val_2)
-------------------------------- # E-add-float
(Call + val_1 val_2)  ~~>  val_3

val_3 = float_add(val_1, val_2)
-------------------------------- # E-sub-float
(Call - val_1 val_2)  ~~>  val_3

val_3 = eq(val_1, val_2)
--------------------------------- # E-builtin-eq
(Call == val_1 val_2)  ~~>  val_3

val_3 = le(val_1, val_2)
--------------------------------- # E-builtin-le
(Call <= val_1 val_2)  ~~>  val_3

val_3 = lt(val_1, val_2)
-------------------------------- # E-builtin-lt
(Call < val_1 val_2)  ~~>  val_3
```

The impure notions of reduction are:
```
l notin C.locs
----------------------------------------------------------- # E-let-introduce
C; (Let x val e)  ~~>  C + locs with l -> copy(val); e[x/l]
# TODO: the location needs to be removed from `C` once e is done evaluating,
#       otherwise it remains accessible. This is not a problem at the moment,
#       but it will be once there are first-class locations (e.g., pointers)
#       in the source language. Removing the location from the store could be
#       achieved via a new `(Pop x)` construct, where `(Let x val e)` reduces
#       to `(Pop x e)`

C; (Asgn l val)  ~~>  C + locs with l -> copy(val); (TupleCons) # E-asgn

val_1 = (proc typ_r [x typ_p]^n e)
---------------------------------------------------------------- # E-call-reduce
(Call val_1 val_2^n)  ~~>  (Frame typ_r e[x/copy(C, val_2) ...])

# ^^ read: the call is replaced with the procedure's body (in which all
# occurrences of the parameters were substituted with a copy of the respective
# argument), which is wrapped in a `Frame` expression
```

The steps are:
```
       e_1 ~~> e_2
-------------------------  # E-reduce-pure
C; E[e_1]  -->  C; E[e_2]

    C_1; e_1 ~~> C_2; e_2
-----------------------------  # E-reduce-impure
C_1; E[e_1]  -->  C_2; E[e_2]

val_2 = copy(val_1)
----------------------------------------------------- # E-return
C; B[(Frame typ E[(Return val_1)])]  -->  C; B[val_2]

B != []
------------------------------------------ # E-unreachable
C; B[(Unreachable)]  -->  C; (Unreachable)
```

#### Auxiliary Functions

Arithmetic functions:
```
int_add(n_1, n_2) = n_1 + n_2  (where -2^63 <= n_1 - n_2 < 2^63)
                  = {}         (otherwise)

int_sub(n_1, n_2) = n_1 - n_2  (where -2^63 <= n_1 - n_2 < 2^63)
                  = {}         (otherwise)

float_add(real_1, real_2) = ?
float_sub(real_1, real_2) = ?

eq(a, b) = (a = b)  (where a : bool v a : int)
         = ?        (where a : float)
lt(a, b) = a < b    (where a : int)
         = ?        (where a : float)
le(a, b) = a < b    (where a : int)
         = ?        (where a : float)
```

> TODO: the floating-point operations need to be defined according to the
>       IEEE 754.2008 standard

The `copy` function takes a context and value and maps them to a value that
is neither a location nor contains any:
```
copy (C, val) -> val

copy(C, c)                 = c
copy(C, l)                 = copy(C, C.locs(l))
copy(C, (Proc typ e))      = (Proc typ e)
copy(C, (TupleCons val^n)) = (TupleCons copy(val)^n)
```

#### Type Safety

The following two guarantees are made:
* for `e` where `e : typ` and `e --> e'`, it follows that `e' : typ` (preservation)
* for `e` where `e : typ`, `e` is either a `val` or there exists an `e --> e'` (progress)

In other words, a well-typed program always reduces to a value, meaning that
the language is *type safe* (in theory, that is. There's no formal proof yet
that this really is the case).
