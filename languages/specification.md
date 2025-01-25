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
strVal   ::= (StringVal <string>)
expr     ::= <ident>
          |  <intVal>
          |  <floatVal>
          |  (TupleCons <expr>*)
          |  (Seq <texpr> <expr>*)
          |  (Seq <strVal>)
          |  (Call <expr>+)
          |  (FieldAccess <expr> <intVal>)
          |  (At <expr> <expr>)
          |  (And <expr> <expr>)
          |  (Or <expr> <expr>)
          |  (If <expr> <expr> <expr>?)
          |  (While <expr> <expr>)
          |  (Return <expr>?)
          |  (Unreachable)
          |  (Exprs <expr>+)
          |  (Asgn <expr> <expr>)
          |  (Decl <ident> <expr>)
          |  (Match <expr> (As <ident> <texpr> <expr>)+)
texpr    ::= <ident>
          |  (VoidTy)
          |  (UnitTy)
          |  (BoolTy)
          |  (IntTy)
          |  (FloatTy)
          |  (TupleTy <texpr>*)
          |  (UnionTy <texpr>+)
          |  (ProcTy <texpr>+)
          |  (SeqTy <texpr>)

param_decl ::= (ParamDecl <ident> <texpr>)
decl       ::= (ProcDecl <ident> <texpr> (Params <param_decl>*) <expr>)
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
ch  ::= ...                         # UTF-8 byte values
c   ::= n                           # corresponds to `(IntVal n)`
     |  rational                    # corresponds to `(FloatVal rational)`
     |  str                         # corresponds to `(StringVal str)`
     |  true                        # corresponds to `(Ident "true")`
     |  false                       # corresponds to `(Ident "false")`
     |  (TupleCons)                 # unit value
     |  (Unreachable)               # an irrecoverable error
l   ::= ...                         # first-class location
val ::= <c>
     |  <l>
     |  (array <val>+)              # array value
     |  (tuple <val>+)              # tuple value
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
     |  (SeqTy   <typ>)
le  ::= <l>                  # | subset of expressions where all non-lvalue
     |  (FieldAccess <le> n) # | operands were already evaluated
     |  (At <le> n)          # |
e   ::= x                    # free variable
     | <val>
     | <typ>
     | (With a:<e> n b:<e>)  # | return array/tuple value `a` with the `n`-th
                             # | element replaced with `b`
     |  ... # includes all expressions from the abstract syntax

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
char  = char
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
void <: char
void <: int
void <: float
void <: (TupleTy typ+)
void <: (UnionTy typ+)
void <: (ProcTy typ+)

typ_1 <: (UnionTy typ_1 typ_2 ...) # | a type is a subtype of `UnionTy` if it's
                                   # | a part of the union (in any position)
```

#### Typing Rules

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

Type expressions use a separate set of rules. They're identified by the
conclusion being a judgment of the form `C |-_t x : typ`.

##### Primitive Types

```

--------------------- # S-void-type
C |-_t (VoidTy) : void


--------------------- # S-unit-type
C |-_t (UnitTy) : unit


--------------------- # S-bool-type
C |-_t (BoolTy) : bool


--------------------- # S-char-type
C |-_t (CharTy) : char


------------------- # S-int-type
C |-_t (IntTy) : int


----------------------- # S-float-type
C |-_t (FloatTy) : float


----------------------- # S-empty-tuple-type
C |-_t (TupleTy) : unit
```

##### Composite Types

```
x in C.symbols  C.symbols(x) = (type typ)
----------------------------------------- # S-type-ident
C |-_t x : typ

C |-_t e : typ ...  typ != void ...
------------------------------------------ # S-tuple-type
C |-_t (TupleTy e+) : (TupleTy typ ...)

C |-_t e : typ ...  typ != void ...  |{typ ...}| = |e| # each type must be unique
------------------------------------------------------ # S-union-type
C |-_t (UnionTy e+) : (UnionTy typ ...)

C |-_t res : typ_1   C |-_t e : typ_2 ...  typ_2 != void ...
------------------------------------------------------------ # S-proc-type
C |-_t (ProcTy res e*) : (ProcTy typ_1 typ_2 ...)

C |-_t e : typ  typ != void
------------------------------ # S-seq-type
C |-_t (SeqTy e) : (SeqTy typ)
```

##### Expressions

Mutability is part of the type system. `All[typ]` means "matches `(mut typ)`
and `typ`", which makes it writing deduction rules applicable to expression of
both mutable and immutable type easier.

`built_ins` is a set of names:
`{==, <=, <, +, -, *, div, mod, true, false, write, writeErr, readFile}`.

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

x in C.symbols  C.symbols(x) = typ  typ != (type ...)
----------------------------------------------------- # S-identifier
C |- x : typ

C |- e : All[typ] ...  typ != void ...
--------------------------------------- # S-tuple
C |- (TupleCons e+) : (TupleTy typ ...)

C |-_t e_1 : typ_1  C |- e_2 : All[typ_2] ...  typ_2 <:= typ_1 ...
------------------------------------------------------------------ # S-seq-cons
C |- (Seq e_1 e_2*) : (SeqTy typ_1)


------------------------------------------------------------------ # S-string-cons
C |- (Seq str) : (SeqTy char)

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

C |- e_1: typ_1  typ_1 = (SeqTy typ_2)  C |- e_2 : typ_3  typ_3 = int
--------------------------------------------------------------------- # S-at
C |- (At e_1 e_2) : typ_2

C |- e: (mut typ_1)  typ_1 = (SeqTy typ_2)  C |- e_2 : typ_3  typ_3 = int
------------------------------------------------------------------------- # S-mut-field
C |- (At e_1 e_2) : (mut typ_2)

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

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ = int
------------------------------------------------------- # S-builtin-mul
C |- (Call * e_1 e_2) : typ_1

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ = int
------------------------------------------------------- # S-builtin-div
C |- (Call div e_1 e_2) : typ_1

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ = int
------------------------------------------------------- # S-builtin-mod
C |- (Call mod e_1 e_2) : typ_1

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ in {int, float, bool}
----------------------------------------------------------------------- # S-builtin-eq
C |- (Call == e_1 e_2) : typ_1

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ in {int, float}
----------------------------------------------------------------- # S-builtin-le
C |- (Call <= e_1 e_2) : bool

C |- e_1 : All[typ_1]  C |- e_2 : All[typ_1]  typ in {int, float}
----------------------------------------------------------------- # S-builtin-lt
C |- (Call < e_1 e_2) : bool

C |- e : All[typ]  typ = (SeqTy ...)
------------------------------------ # S-builtin-len
C |- (Call len e) : int

C |- e_1 : All[typ_1]  typ_1 = (SeqTy typ_2)  C |- e_2 : All[typ_3]  typ_3 <:= typ_2
------------------------------------------------------------------------------------ # S-builtin-concat
C |- (Call concat e_1 e_2) : typ_1

C |- e_1 : All[typ]  typ = (SeqTy char)
--------------------------------------- # S-builtin-write
C |- (Call write e_1) : unit

C |- e_1 : All[typ]  typ = (SeqTy char)
--------------------------------------- # S-builtin-writeErr
C |- (Call writeErr e_1) : unit

C |- e_1 : All[typ]  typ = (SeqTy char)
--------------------------------------- # S-builtin-readFile
C |- (Call readFile e_1) : (SeqTy char)

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
C |- (Frame typ_1 e) : typ_1


--------------------------------------------------------- # S-proc-val
C |- (proc typ_r [x typ_p]^ e) : (ProcTy typ_r typ_p ...)

C |- e_1 : All[typ_1]  typ_1 = (SeqTy typ_2)  C |- e_2 : All[typ_3]  typ_3 <:= typ_2
------------------------------------------------------------------------------------ # S-seq-with
C |- (With e_1 n e_2) : typ_1

C |- e_1 : All[typ_1]  typ_1 = (TupleTy typ_2+)  C |- e_2 : All[typ_3]  typ_3 <:= typ_2 at n
-------------------------------------------------------------------------------------------- # S-tuple-with
C |- (With e_1 n e_2) : typ_1
```

##### Modules and Declarations

Top-level declarations use slightly different judgments, of the form:
```
C_1 |- e --> C_2
```
which is read as "under context `C_1`, `e` *steps to* context `C_2`".

```
C |-_t e : typ
-------------------------------------------------------- # S-type-decl
C |- (TypeDecl x e) --> C + symbols with x -> (type typ)

x_1 notin C.symbols  x_1 != x_2 ...  x_2 notin C.symbols  |x_2| = |{x_2 ...}|  C |-_t e_1 : typ_1
C |- e_2 : typ_2 ...  typ_2 != void ...  p = (ProcTy typ_1 typ_2 ...)
C + return = typ + symbols with x_1 -> p, x_2 -> typ_2 ... |- e : void
---------------------------------------------------------------------------------------------------- # S-proc-decl
C |- (ProcDecl x_1 e_1 (Params (ParamDecl x_2 e_2)*) e_3) --> C + symbols with x_1 -> p


-------------------- # S-empty-module
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
C ::= { locs S
        output val
        errOutput val }
```

`locs` is a store (`S`), which maps *locations* to *values* (`S(l) = val`).
Mutable state is modeled via locations.

`input` is a value, which must be a `(array c ...)`, where `c` is of type
`char`. The same is true for both `output` and `errOutput`.

`e[x/y]` means "`e` with all occurrences of name `x` replaced with `y`".

It is assumed that all identifiers referring to procedures were replaced with
`(proc r [x p]* body)` prior to evaluation, where `x` and `p` are the names
and types of the procedure's parameters, `r` is the procedure's return type,
and `body` is the procedure's body.

> TODO: the assumption above should be baked into the static semantics
>       somehow...

> TODO: the static semantics also needs to describe how a `(Module ...)` is
>       reduced to a `(proc ...)` value, which is what a program is, in the
>       end -- a procedural value

The evaluation contexts are:

```
E' ::= (FieldAccess E' n)
    |  (At E' e)
    |  (At le E)

L  ::= []                  # | evaluation context for lvalues
    |  (FieldAccess L n)   # |
    |  (At L n)            # |

E  ::= []
    |  (Exprs E e*)
    |  (FieldAccess E n)
    |  (At E e)
    |  (At le E)
    |  (Asgn E' e)
    |  (Asgn le E)
    |  (With E n e)
    |  (With val n E)
    |  (TupleCons val* E e*)
    |  (Seq typ val* E e*)
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

(FieldAccess (tuple val^n) i)  ~~>  val_i # E-tuple-access

(Asgn (FieldAccess le n) val_1)  ~~>  (Asgn le (With le n val_1)) # E-field-asgn
(Asgn (At le n) val_1)           ~~>  (Asgn le (With le n val_1)) # E-elem-asgn

n >= 0  n < |val|
---------------------------------- # E-at
(At (array val*) n)  ~~>  val at n

n < 0 v n >= |val|
-------------------------------------- # E-at-out-of-bounds
(At (array val*) n)  ~~> (Unreachable)

n >= 0  n < |val_1|  val_3 = copy(C, val_1) with n -> copy(val_2)
----------------------------------------------------------------- # E-with
C; (With val_1 n val_2)  ~~>  C; val_3

n < 0 v n >= |val_1|
------------------------------------------------------------------ # E-with-out-of-bounds
C; (With val_1 n val_2)  ~~>  C; (Unreachable)

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

val = int_mul(n_1, n_2)
-------------------------- # E-mul-int
(Call * n_1 n_2)  ~~>  val

int_mul(n_1, n_2) = {}
------------------------------------ # E-mul-int-overflow
(Call * n_1 n_2)  ~~>  (Unreachable)

val = int_div(n_1, n_2)
---------------------------- # E-div-int
(Call div n_1 n_2)  ~~>  val

int_div(n_1, n_2) = {}
-------------------------------------- # E-div-int-overflow
(Call div n_1 n_2)  ~~>  (Unreachable)

val = int_mod(n_1, n_2)
---------------------------- # E-mod-int
(Call mod n_1 n_2)  ~~>  val

int_mod(n_1, n_2) = {}
-------------------------------------- # E-mod-int-error
(Call mod n_1 n_2)  ~~>  (Unreachable)

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

length = |val|
--------------------------- # E-builtin-len
(Call len val)  ~~>  length

---------------------------------------------------------------- # E-builtin-concat
(Call concat (array val_1*) val_2)  ~~>  (array val_1 ... val_2)

val_2 = (array ch*)
--------------------------------- # E-builtin-readFile
(Call readFile val_1)  ~~>  val_2

# ^^ a readFile call doesn't reduce to a concrete value, but rather to an
# abstract value. The only thing known about the abstract value is that it's
# an array with an unknown number of elements belonging to the `ch` non-
# terminal
```

The impure notions of reduction are:
```
val_2 = copy(C, val_1) ...
------------------------------------------------ # E-tuple-cons
C; (TupleCons val_1+)  ~~>  C; (tuple val_2 ...)

val_2 = copy(C, val_1) ...
---------------------------------------------- # E-seq-cons
C; (Seq typ val_1+)  ~~>  C; (array val_2 ...)

ch in utf8_bytes(str)
------------------------------------ # E-string-cons
C; (Seq str)  ~~>  C; (array ch ...)

l notin C.locs
-------------------------------------------------------------- # E-let-introduce
C; (Let x val e)  ~~>  C + locs with l -> copy(C, val); e[x/l]
# TODO: the location needs to be removed from `C` once e is done evaluating,
#       otherwise it remains accessible. This is not a problem at the moment,
#       but it will be once there are first-class locations (e.g., pointers)
#       in the source language. Removing the location from the store could be
#       achieved via a new `(Pop x)` construct, where `(Let x val e)` reduces
#       to `(Pop x e)`

C; (Asgn l val)  ~~>  C + locs with l -> copy(C, val); (TupleCons) # E-asgn

val_1 = (proc typ_r [x typ_p]^n e)
---------------------------------------------------------------- # E-call-reduce
(Call val_1 val_2^n)  ~~>  (Frame typ_r e[x/copy(C, val_2) ...])

# ^^ read: the call is replaced with the procedure's body (in which all
# occurrences of the parameters were substituted with a copy of the respective
# argument), which is wrapped in a `Frame` expression

C_1.output = (array val_2*)  C_2 = C_1 with output = (array val_2 ... val_1 ...)
-------------------------------------------------------------------------------- # E-builtin-write
C_1; (Call write val_1)  ~~>  C_2; (TupleCons)

C_1.errOutput = (array val_2*)  C_2 = C_1 with errOutput = (array val_2 ... val_1 ...)
-------------------------------------------------------------------------------------- # E-builtin-writeErr
C_1; (Call writeErr val_1)  ~~>  C_2; (TupleCons)
```

The steps are:
```
       e_1 ~~> e_2
-------------------------  # E-reduce-pure
C; E[e_1]  -->  C; E[e_2]

    C_1; e_1 ~~> C_2; e_2
-----------------------------  # E-reduce-impure
C_1; E[e_1]  -->  C_2; E[e_2]

C.locs(l) = val
------------------------------------------------------------ # E-tuple-loc-access
C; E[L[(FieldAccess l n)]  ~~>  C; E[L[(FieldAccess val n)]]

C.locs(l) = val
------------------------------------------ # E-at-loc
C; E[L[(At l n)]  ~~>  C; E[L[(At val n)]]

val_2 = copy(C, val_1)
----------------------------------------------------- # E-return
C; B[(Frame typ E[(Return val_1)])]  -->  C; B[val_2]

----------------------------------------------------- # E-return-unit
C; B[(Frame typ E[(Return)])]  -->  C; B[(TupleCons)]

B != []
------------------------------------------ # E-unreachable
C; B[(Unreachable)]  -->  C; (Unreachable)
```

#### Auxiliary Functions

Arithmetic functions:
```
trunc(r) = +i (where r >= 0 ^ i in N ^ |r| - 1 < i <= |r|)
         = -i (where r <  0 ^ i in N ^ |r| - 1 < i <= |r|)
# ^^ round towards zero

int_add(n_1, n_2) = n_1 + n_2  (where -2^63 <= n_1 - n_2 < 2^63)
                  = {}         (otherwise)

int_sub(n_1, n_2) = n_1 - n_2  (where -2^63 <= n_1 - n_2 < 2^63)
                  = {}         (otherwise)

int_mul(n_1, n_2) = n_1 * n_2  (where -2^63 <= n_1 * n_2 < 2^63)
                  = {}         (otherwise)

int_div(n_1, 0)   = {}
int_div(n_1, n_2) = {}                (where n_1 = -2^63 ^ n_2 = -1)
                  = trunc(n_1 / n_2)  (otherwise)

int_mod(n_1, 0)   = {}
int_mod(n_1, n_2) = n_1 - (n_2 * trunc(n_1 / n_2))

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

copy(C, c)                        = c
copy(C, l)                        = copy(C, C.locs(l))
copy(C, (proc typ_r [x typ]^n e)) = (proc typ_r [x typ]^n e)
copy(C, (array val^n))            = (array val^n)
copy(C, (tuple val^n))            = (tuple val^n)
```

```
utf8_bytes(str) = ?
# TODO: the function is mostly self-explanatory, but it should be defined in
#       a bit more detail nonetheless
```

#### Type Safety

The following two guarantees are made:
* for `e` where `e : typ` and `e --> e'`, it follows that `e' : typ` (preservation)
* for `e` where `e : typ`, `e` is either a `val` or there exists an `e --> e'` (progress)

In other words, a well-typed program always reduces to a value, meaning that
the language is *type safe* (in theory, that is. There's no formal proof yet
that this really is the case).
