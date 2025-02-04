## Provides the formal definition for the source language, written using
## Phy's meta-language.
##
## This is the one and only authoritative definition of the source language.
##
## As with most language-related things, the language definition is a
## **work in progress**.
##
## **Important:** as is, the language definition **does not** match
## the originally intended semantics, and thus does not model the behaviour
## of the implementation. This'll be fixed eventually.

import
  spec/[langdefs, types]

const lang* = language:
  alias n, z
  # TODO: remove `n` and use `z` directly. `n` usually refers to *natural*
  #       numbers, not *integer* numbers
  typ ident: Ident(string)
  alias x, ident
  typ expr:
    IntVal(z)
    FloatVal(r)
    TupleCons(*expr)
    Seq(texpr, *expr)
    StringVal(string)
    Seq(StringVal(symbol))
    Call(+expr)
    FieldAccess(expr, IntVal(z))
    At(expr, expr)
    And(expr, expr)
    Or(expr, expr)
    If(expr, expr, expr)
    If(expr, expr)
    While(expr, expr)
    Return(expr)
    Return()
    Unreachable()
    Exprs(+expr)
    Asgn(expr, expr)
    Decl(ident, expr)

    Let(ident, expr, expr)

    # syntax not available at the source level:
    true
    false
    char(z) # UTF-8 byte
    loc(z) # first-class location
    `array`(+val)
    `tuple`(+val)
    `proc`(typ, *[x, typ], e)

    With(e, n, e) # return a tuple/array value with the n-th element replaced
    Frame(typ, e) # a special expression for assisting with evaluation

  alias e, expr

  typ texpr:
    Ident(string)
    VoidTy()
    UnitTy()
    BoolTy()
    CharTy()
    IntTy()
    FloatTy()
    TupleTy(*texpr)
    UnionTy(+texpr)
    ProcTy(+texpr)
    SeqTy(texpr)

    # type expressions not available at the source level
    mut(texpr)
    `type`(texpr)

  alias typ, texpr

  typ paramDecl:
    ParamDecl(ident, texpr)
  typ decl:
    ProcDecl(ident, texpr, Params(*paramDecl), expr)
    TypeDecl(ident, texpr)
  typ module:
    Module(*decl)

  subtype val, e:
    ## A value is an irreducible expression.
    true
    false
    char(z)
    loc(z)
    `array`(+val)
    `tuple`(+val)
    `proc`(typ, *[x, typ], e)

  subtype le, e:
    ## Lvalue expression with all non-lvalue operands already evaluated.
    l
    FieldAccess(le, n)
    At(le, n)

  function desugar, expr -> e:
    # FIXME: the sub-expressions need to be desugared too!
    case _
    of And(expr_1, expr_2):
      If(expr_1, expr_2, false)
    of Or(expr_1, expr_2):
      If(expr_1, true, expr_2)
    of Decl(x_1, expr_1):
      Let(x_1, expr_1, TupleCons())
    of Exprs(*expr_1, Decl(x_1, expr_2), +expr_3):
      Exprs(...expr_1, Let(x_1, expr_2, Exprs(...expr_3)))
    of If(expr_1, expr_2):
      If(expr_1, expr_2, TupleCons())
    of If(Exprs(*expr_1, expr_2), expr_3, expr_4):
      Exprs(...expr_1, If(expr_2, expr_3, expr_4))

  ## Type Relations
  ## --------------

  inductive `<:`(inp typ, inp typ), "$1 <: $2":
    ## :math:`<:` is the subtype relationship operator. :math:`a <: b` means
    ## ":math:`a` is a subtype of :math:`b`"
    rule "void":
      ## :math:`\text{void}` is the subtype of all other types, except for
      ## itself.
      condition typ_1 != VoidTy()
      conclusion VoidTy(), typ_1
    rule "union-subtyping":
      ## A type is a subtype of a union if it's a part of the union (in
      ## any position).
      condition typ_1 in typ_2
      conclusion typ_1, UnionTy(*typ_2)

  inductive `==`(inp typ, inp typ), "$1 = $2":
    ## Except for union types, all type equality uses *structural equality*.
    axiom "", typ, typ # same structure, equal type
    rule "union":
      # order of types is not significant
      condition set(typ_1) == set(typ_2)
      conclusion UnionTy(+typ_1), UnionTy(+typ_2)

  inductive `!=`(inp typ, inp typ), "":
    rule "":
      condition not(typ_1 == typ_2)
      conclusion typ_1, typ_2

  inductive `<:=`(inp typ, inp typ), "$1 <:= $2":
    ## :math:`<:=` is the "sub or equal type" operator.
    rule "equal":
      condition typ_1 == typ_2
      conclusion typ_1, typ_2
    rule "subtype":
      condition typ_1 <:= typ_2
      conclusion typ_1, typ_2

  ## Typing Judgment
  ## ---------------
  ##
  ## The language's static semantics consist of typing judgements, relating a
  ## symbol context and abstract syntax expression to a type.

  record C, (symbols: (loc -> typ), ret: typ)
  ## :math:`C` is the symbol environment.

  context All:
    # Convenience context that is used where both mutable and non
    # mutable types are allowed.
    hole
    mut(hole)

  function common, (typ, typ) -> typ:
    ## Computes the closest common ancestor type for a type pair. The function
    ## is not total, as not all two types have a common ancestor type.
    case _
    of typ_1, typ_2:
      if typ_1 == typ_2:   typ_1
      elif typ_1 <: typ_2: typ_2
      elif typ_2 <: typ_1: typ_1

  inductive ttypes(inp C, inp texpr, out typ), "$1 \\vdash_{\\tau} $2 : $3":
    axiom "S-void-type",        C, VoidTy(),  VoidTy()
    axiom "S-unit-type",        C, UnitTy(),  UnitTy()
    axiom "S-bool-type",        C, BoolTy(),  BoolTy()
    axiom "S-char-type",        C, CharTy(),  CharTy()
    axiom "S-int-type",         C, IntTy(),   IntTy()
    axiom "S-float-type",       C, FloatTy(), FloatTy()
    axiom "S-empty-tuple-type", C, TupleTy(), UnitTy()

    rule "S-type-ident":
      condition x_1 in C_1.symbols
      where type(typ_1), C_1.symbols(x_1)
      conclusion C_1, x_1, typ_1

    rule "S-tuple-type":
      premise ...ttypes(C_1, texpr_1, typ_1)
      condition ...(typ_1 != VoidTy())
      conclusion C_1, TupleTy(+texpr_1), TupleTy(...typ_1)

    rule "S-union-type":
      premise ...ttypes(C_1, texpr_1, typ_1)
      condition ...(typ_1 != VoidTy())
      condition len(set(typ_1)) == len(typ_1) # there must be no duplicate types
      conclusion C_1, UnionTy(+texpr_1), TupleTy(typ_1)

    rule "S-proc-type":
      premise ttypes(C_1, texpr_1, typ_1)
      premise ...ttypes(C_1, texpr_2, typ_2)
      condition ...(typ_2 != VoidTy())
      conclusion C_1, ProcTy(texpr_1, *texpr_2), ProcTy(typ_1, typ_2)

    rule "S-seq-type":
      premise ttypes(C_1, texpr_1, typ_1)
      condition ...(typ_1 != VoidTy())
      conclusion C_1, SeqTy(texpr_1), SeqTy(typ_1)

  alias built_in,
    {"==", "<=", "<", "+", "-", "*", "div", "mod", "true", "false", "write",
     "writeErr", "readFile"}

  inductive types(inp C, inp e, out typ), "$1 \\vdash $2 : $3":
    axiom "S-int",   C, n, IntTy()
    axiom "S-float", C, r, FloatTy()
    axiom "S-false", C, false, BoolTy()
    axiom "S-true",  C, true, BoolTy()
    axiom "S-unit",  C, TupleCons(), UnitTy()
    axiom "S-unreachable", C, Unreachable(), VoidTy()

    rule "S-identifier":
      condition x_1 in C_1.symbols
      where typ_1, C_1.symbols(x_1)
      where !type(any), typ_1 # normal identifiers don't bind types
      conclusion C_1, x_1, typ_1

    rule "S-tuple":
      premise ...types(C_1, e_1, All[typ_1])
      condition ...(typ_1 != VoidTy())
      conclusion C_1, TupleCons(+e_1), TupleTy(typ_1)

    rule "S-seq-cons":
      premise ttypes(C_1, texpr_1, typ_1)
      premise ...types(C_1, e_2, typ_2)
      condition ...(typ_2 <:= typ_1)
      conclusion C_1, Seq(texpr_1, *e_2), SeqTy(typ_1)

    axiom "S-string-cons", C, Seq(StringVal(string)), SeqTy(CharTy())

    rule "S-return":
      premise types(C_1, e_1, All[typ_1])
      condition typ_1 <:= C_1.ret
      conclusion C_1, Return(e_1), VoidTy()

    rule "S-return-unit":
      condition C_1.ret == UnitTy()
      conclusion C_1, Return(), VoidTy()

    rule "S-field":
      premise types(C_1, e_1, typ_1)
      where TupleTy(+any), typ_1
      where typ_2, typ_1[n_1]
      conclusion C_1, FieldAccess(e_1, IntVal(n_1)), typ_2

    rule "S-mut-field":
      premise types(C_1, e_1, mut(typ_1))
      where TupleTy(+any), typ_1
      where typ_2, typ_1[n_1]
      conclusion C_1, FieldAccess(e_1, IntVal(n_1)), mut(typ_2)

    rule "S-at":
      premise types(C_1, e_1, typ_1)
      premise types(C_1, e_2, All[IntTy()])
      where SeqTy(typ_2), typ_1
      conclusion C_1, At(e_1, e_2), typ_2

    rule "S-mut-at":
      premise types(C_1, e_1, mut(typ_1))
      premise types(C_1, e_2, All[IntTy()])
      where SeqTy(typ_2), typ_1
      conclusion C_1, At(e_1, e_2), mut(typ_2)

    rule "S-asgn":
      premise types(C_1, e_1, mut(typ_1))
      premise types(C_1, e_2, All[typ_2])
      condition typ_2 <:= typ_1
      conclusion C_1, Asgn(e_1, e_2), UnitTy()

    rule "S-let":
      condition x_1 notin C_1.symbols
      condition x_1 notin built_in
      premise types(C_1, e_1, All[typ_1])
      let C_2 = C_1 + C(symbols: {x_1: mut(typ_1)})
      premise types(C_2, e_2, All[typ_2])
      conclusion C_1, Let(x_1, e_1, e_2), typ_2

    rule "S-exprs":
      premise ...types(C_1, e_1, All[UnitTy()])
      premise types(C_1, e_2, typ_2)
      conclusion C_1, Exprs(*e_1, e_2), typ_2

    rule "S-void-short-circuit":
      # if any expression in the list is of type void, so is the list itself
      premise ...types(C_1, e_1, All[e_3])
      condition ...(e_3 in {VoidTy(), UnitTy()})
      condition VoidTy() in e_3
      premise types(C_1, e_2, typ)
      conclusion C_1, Exprs(*e_1, e_2), VoidTy()

    rule "S-if":
      premise types(C_1, e_1, All[BoolTy()])
      premise types(C_1, e_2, All[typ_1])
      premise types(C_1, e_3, All[typ_2])
      let typ_3 = common(typ_1, typ_2)
      conclusion C_1, If(e_1, e_2, e_3), typ_3

    rule "S-while":
      premise types(C_1, e_1, All[BoolTy()])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 in {VoidTy(), UnitTy()}
      conclusion C_1, While(e_1, e_2), UnitTy()

    rule "S-while":
      premise types(C_1, e_1, All[typ_1])
      condition typ_1 in {VoidTy(), UnitTy()}
      conclusion C_1, While(true, e_1), VoidTy()

    rule "S-builtin-plus":
      premise types(C_1, e_1, All[typ_1])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call(Ident("+"), e_1, e_2), typ_1

    rule "S-builtin-minus":
      premise types(C_1, e_1, All[typ_1])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call(Ident("-"), e_1, e_2), typ_1

    rule "S-builtin-mul":
      premise types(C_1, e_1, All[typ_1])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 == IntTy()
      conclusion C_1, Call(Ident("*"), e_1, e_2), typ_1

    rule "S-builtin-div":
      premise types(C_1, e_1, All[typ_1])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 == IntTy()
      conclusion C_1, Call("div", e_1, e_2), typ_1

    rule "S-builtin-eq":
      premise types(C_1, e_1, All[typ_1])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 in {BoolTy(), IntTy(), FloatTy()}
      conclusion C_1, Call("==", e_1, e_2), BoolTy()

    rule "S-builtin-lt":
      premise types(C_1, e_1, All[typ_1])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call("<", e_1, e_2), BoolTy()

    rule "S-builtin-le":
      premise types(C_1, e_1, All[typ_1])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call("<=", e_1, e_2), BoolTy()

    rule "S-builtin-mod":
      premise types(C_1, e_1, All[typ_1])
      premise types(C_1, e_2, All[typ_1])
      condition typ_1 == IntTy()
      conclusion C_1, Call("mod", e_1, e_2), typ_1

    rule "S-builtin-len":
      premise types(C_1, e_1, All[SeqTy(typ)])
      conclusion C_1, Call("len", e_1), IntTy()

    rule "S-builtin-concat":
      premise types(C_1, e_1, All[SeqTy(typ_1)])
      premise types(C_1, e_2, All[typ_2])
      condition typ_2 <:= typ_1
      conclusion C_1, Call("concat", e_1, e_2), UnitTy()

    rule "S-builtin-write":
      premise types(C_1, e_1, All[SeqTy(CharTy())])
      conclusion C_1, Call("write", e_1), UnitTy()

    rule "S-builtin-writeErr":
      premise types(C_1, e_1, All[SeqTy(CharTy())])
      conclusion C_1, Call("writeErr", e_1), UnitTy()

    rule "S-builtin-readFile":
      premise types(C_1, e_1, All[SeqTy(CharTy())])
      conclusion C_1, Call("readFile", e_1), SeqTy(CharTy())

    rule "S-call":
      premise types(C_1, e_1, All[typ_1])
      where ProcTy(typ_r, *typ_p), typ_1
      premise ...types(C_1, e_2, All[typ_a])
      condition ...(typ_a <:= typ_p)
      conclusion C_1, Call(e_1, *e_2), typ_r

    rule "S-Frame":
      premise types(C_1, e_1, typ_2)
      condition typ_2 <:= typ_1
      conclusion C_1, Frame(typ_1, e_1), typ_1

    rule "S-proc-val":
      conclusion C_1, `proc`(typ_r, *[x, typ_p], e), ProcTy(typ_r, ...typ_p)

    rule "S-seq-with":
      premise ttypes(C_1, e_1, All[typ_1])
      premise ttypes(C_1, e_2, All[typ_3])
      where SeqTy(typ_2), typ_1
      condition typ_3 <:= typ_2
      conclusion C_1, With(e_1, n_1, e_2), typ_1

    rule "S-tuple-with":
      premise ttypes(C_1, e_1, All[typ_1])
      premise ttypes(C_1, e_2, All[typ_2])
      where TupleTy(+typ), typ_1
      where typ_3, typ_1[n_1]
      condition typ_2 <:= typ_3
      conclusion C_1, With(e_1, n_1, e_2), typ_3

  inductive toplevel(inp C, inp decl, out C), "$1 \\vdash $2 \\Rightarrow $3":
    rule "S-type-decl":
      premise ttypes(C_1, e_1, typ_1)
      where C_2, C_1 + {"symbols": {x_1: type(typ_1)}}
      conclusion C_1, TypeDecl(x_1, e_1), C_2

    rule "S-proc-decl":
      condition x_1 notin C_1.symbols
      condition len({x_1} + { ...x_2 }) == 1 + len(x_2) # all symbols must be unique
      premise ttypes(C_1, e_1, typ_1)
      premise ...ttypes(C_1, e_2, typ_2)
      condition ...(typ_2 != VoidTy())
      let typ_3 = ProcTy(typ_1, ...typ_2)
      let C_2 = C_1 + C(symbols: {x_1: typ_3})
      let C_3 = C_2 + C(`return`: typ_1, symbols: { ...x_2: ...typ_2 })
      premise types(C_3, e_3, VoidTy())
      conclusion C_1, ProcDecl(x_1, e_1, Params(*ParamDecl(x_2, e_2)), e_3), C_2

    axiom "S-empty-module", C_1, Module(), C_1

    rule "S-module":
      premise toplevel(C_1, decl_1, C_2)
      premise toplevel(C_2, Module(...decl_2), C_3)
      conclusion C_1, Module(decl_1, *decl_2), C_3

  # TODO: the static semantics also needs to describe how a `(Module ...)` is
  #      reduced to a `(proc ...)` value, which is what a program is, in the
  #      end: a procedural value

  ## Dynamic Semantics
  ## -----------------
  ##
  ## The semantics describing how expressions reduce to values.
  ##
  ## It is assumed that all identifiers referring to procedures were replaced
  ## with `(proc r [x p]* body)` prior to evaluation, where `x` and `p` are
  ## the names and types of the procedure's parameters, `r` is the procedure's
  ## return type, and `body` is the procedure's body.
  # TODO: ^^ this must be made explicit in the semantics

  ## Auxiliary Functions
  ## ~~~~~~~~~~~~~~~~~~~

  function substitute, (e, +[x, e]) -> (e, +[x, e]):
    ## The substitution function, which handles binding values/expressions to
    ## identifiers. Identifiers cannot be shadowed.
    case _
    of e_1, ():
      e_1 # nothing more to substitute
    of Exprs(+e_1), +any_2:
      Exprs(...(substitute(e_1, any_2)))
    of Let(ident_1, e_1, e_2), +any_1:
      Let(ident_1, substitute(e_1, any_1), substitute(e_2, any_1))
    of If(e_1, e_2, e_3), +any_1:
      If(substitute(e_1, any_1), substitute(e_2, any_1), substitute(e_3, any_1))
    # TODO: handle the remaining trees
    of Ident(string_1), *[!string_1, _], [string_1, e_1], *[!string_1, _]:
      e_1 # the actual substitution
    of e_1, +any:
      e_1 # nothing to replace

  function trunc, r -> n:
    ## Round towards zero.

  function intAdd, (n, n) -> n:
    case _
    of n_1, n_2:
      let n_3 = n_1 + n_2
      if n_3 <= (2 ^ 63):
        if n_3 < (2 ^ 63):
          n_3
        else:
          fail
      else:
        fail

  function intSub, (n, n) -> n:
    case _
    of n_1, n_2:
      let n_3 = n_1 - n_2
      if n_3 <= (2 ^ 63):
        if n_3 < (2 ^ 63):
          n_3
        else:
          fail
      else:
        fail

  function intMul, (n, n) -> n:
    case _
    of n_1, n_2:
      let n_3 = n_1 * n_2
      if n_3 <= (2 ^ 63):
        if n_3 < (2 ^ 63):
          n_3
        else:
          fail
      else:
        fail

  function intDiv, (n, n) -> n:
    case _
    of n_1, 0: fail
    of n_1, n_2:
      if n_1 == (-2 ^ 63):
        if n_2 == -1:
          fail
        else:
          trunc(n_1 / n_2)
      else:
        trunc(n_1 / n_2)

  function intMod, (n, n) -> n:
    case _
    of n_1, 0: fail
    of n_1, n_2: n_1 - (n_2 * trunc(n_1 / n_2))

  function float_add, (r, r) -> r:
    ## XXX: not defined
  function float_sub, (r, r) -> r:
    ## XXX: not defined

  function valEq, (val, val) -> val:
    case _
    of val_1, val_1: "true"
    else:            "false"

  function lt, (val, val) -> val:
    case _
    of n_1, n_2:
      condition n_1 < n_2
      "true"
    of r_1, r_2:
      condition r_1 < r_2
      "true"
    else: "false"

  function lessEqual, (val, val) -> val:
    case _
    of val_1, val_2:
      where "true", valEq(val_1, val_2)
      "true"
    of val_1, val_2:
      where "true", lt(val_1, val_2)
      "true"
    else: "false"

  # TODO: the floating-point operations need to be defined according to the
  #       IEEE 754.2008 standard

  function copy, (C, val) -> val:
    ## The `copy` function takes a context and value and maps them to a value
    ## that is neither a location nor contains any.
    case _
    of DC_1, l_1: copy(DC_1, DC_1.locs(l_1))
    of DC, val_1: val_1

  function utf8_bytes, x -> (+ch,):
    # TODO: the function is mostly self-explanatory, but it should be defined in
    #       a bit more detail nonetheless
    ##

  function len, (val) -> z:
    ## Computes the number of elements in an array value.
    case _
    of `array`(): 0
    of `array`(val_1, *val_2): 1 + len(...val_2)

  ## Evaluation Contexts
  ## ~~~~~~~~~~~~~~~~~~~

  context Etick:
    FieldAccess(Etick, n)
    At(Etick, e)
    At(le, E)

  context L:
    # evaluation context for lvalues
    hole
    FieldAccess(L, n)
    At(L, n)
  context E:
    hole
    Exprs(E, *e)
    FieldAccess(E, n)
    At(E, e)
    At(le, E)
    Asgn(Etick, e)
    With(E, n, e)
    With(val, n, E)
    TupleCons(*val, E, *e)
    Seq(typ, *val, E, *e)
    Call(*val, E, *e)
    Call(x, *val, E, *e)
    If(E, e, e)
    Let(x, E, e)
    Return(E)

  context B:
    hole
    E[B]
    Frame(typ, B)

  ## Reductions and Steps
  ## ~~~~~~~~~~~~~~~~~~~~

  inductive pReducesTo(inp e, out e), "$1 ~~> $2":
    # pure reductions, that is, reductions not dependent on the execution
    # context
    axiom "E-exprs-fold", Exprs(val_1), val_1
    axiom "E-exprs", Exprs(TupleCons(), +e_1), Exprs(...e_1)
    axiom "E-if-true", If(true, e_1, e_2), e_1
    axiom "E-if-false", If(false, e_1, e_2), e_2

    axiom "E-while", While(e_1, e_2), If(e_1, Exprs(e_2, While(e_1, e_2)), TupleCons())

    rule "E-tuple-access":
      where `tuple`(+val), val_1
      where val_2, val_1[n_1]
      conclusion FieldAccess(val_1, n_1), val_2

    axiom "E-field-asgn", Asgn(FieldAccess(le_1, n_1), val_1), Asgn(le_1, With(le_1, n_1, val_1))
    axiom "E-elem-asgn", Asgn(At(le_1, n_1), val_1), Asgn(le_1, With(le_1, n_1, val_1))

    rule "E-at":
      condition 0 <= n_1
      condition n_1 < len(val_1)
      let val_2 = val_1[n_1]
      conclusion At(val_1, n_1), val_2

    rule "E-at-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion At(val_1, n_1), Unreachable()

    rule "E-with-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion With(val_1, n_1, val_2), Unreachable()

    rule "E-add-int":
      let n_3 = addInt(n_1, n_2)
      conclusion Call("+", IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-add-int-overflow":
      condition (n_1, n_2) notin addInt(n_1, n_2)
      conclusion Call("+", IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-sub-int":
      let n_3 = subInt(n_1, n_2)
      conclusion Call("-", IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-sub-int-overflow":
      condition (n_1, n_2) notin subInt(n_1, n_2)
      conclusion Call("-", IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-mul-int":
      let n_3 = mulInt(n_1, n_2)
      conclusion Call("*", IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-mul-int-overflow":
      condition (n_1, n_2) notin mulInt
      conclusion Call("*", IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-div-int":
      let n_3 = divInt(n_1, n_2)
      conclusion Call("div", IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-div-int-overflow":
      condition (n_1, n_2) notin divInt
      conclusion Call("div", IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-mod-int":
      let n_3 = divInt(n_1, n_2)
      conclusion Call("div", IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-mod-int-overflow":
      condition (n_1, n_2) notin divInt
      conclusion Call("div", IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-add-float":
      let r_3 = floatAdd(r_1, r_2)
      conclusion Call("+", FloatVal(r_1), FloatVal(r_2)), FloatVal(r_3)
    rule "E-sub-float":
      let r_3 = floatSub(r_1, r_2)
      conclusion Call("-", FloatVal(r_1), FloatVal(r_2)), FloatVal(r_3)

    rule "E-builtin-eq":
      let val_3 = valEq(val_1, val_2)
      conclusion Call("==", val_1, val_2), val_3
    rule "E-builtin-le":
      let val_3 = lessEqual(val_1, val_2)
      conclusion Call("<=", val_1, val_2), val_3
    rule "E-builtin-lt":
      let val_3 = lt(val_1, val_2)
      conclusion Call("<", val_1, val_2), val_3

    rule "E-builtin-len":
      let n_1 = len(val_1)
      conclusion Call("len", val_1), n_1

    rule "E-builtin-concat":
      conclusion Call("concat", `array`(*val_1), val_2), `array`(...val_1, val_2)

    rule "E-builtin-readFile":
      exists val_1, z_1,
        val_1 is array and val_1(z_1) is ch
      conclusion Call("readFile", val), val_1

    rule "E-call-reduce":
      # the call is replaced with the procedure's body (in which all
      # occurrences of the parameters were substituted with a copy of the
      # respective argument), which is wrapped in a `Frame` tree
      where `proc`(typ_r, *[x_1, typ_p], e_1), val_1
      where e_2, substitute(e_1, ...[x_1, val_2])
      conclusion Call(val_1, *val_2), Frame(typ_r, e_2)

  inductive reducesTo(inp C, inp e, out C, out e), "$1; $2 ~~> $3; $4":
    rule "E-tuple-cons":
      where +val_2, ...copy(C_1, val_1)
      conclusion C_1, TupleCons(+val_1), C_1, `tuple`(...val_2)

    rule "E-seq-cons":
      where +val_2, ...copy(C_1, val_1)
      conclusion C_1, Seq(typ, val_1), C_1, `array`(...val_2)

    rule "E-string-cons":
      where (*val_1,), utf8_bytes(x_1)
      # FIXME: doesn't need to be an impure reduction
      conclusion C_1, Seq(StringVal(x_1)), C_1, `array`(...val_1)

    rule "E-let-introduce":
      exists z_1, z_1 notin C_1.locs
      let val_2 = copy(DC_1, val_1)
      let C_2 = C_1 + C(locs: {z_1 : val_2})
      let e_2 = substitute(e_1, x_1, loc(z_1))
      conclusion C_1, Let(x_1, val_1, e_1), C_2, e_2
    # TODO: the location needs to be removed from the execution context once
    #       `e_2` is reduced to a value, otherwise it remains accessible. This
    #       is not a problem at the moment, but it will be once there are
    #       first-class locations (e.g., pointers) in the source language.
    #       Removing the location from the store could be achieved via a new
    #       `(Pop x)` construct, where `(Let x val e)` reduces to `(Pop x e)`

    rule "E-with":
      condition 0 <= n_1
      condition n_1 < len(val_1)
      let val_3 = val_1[n_1]
      conclusion C_1, With(val_1, n_1, val_2), C_1, val_3

    rule "E-asgn":
      let C_2 = C_1 + C(locs: {z_1 : val_1})
      conclusion C_1, Asgn(z_1, val_1), C_2, TupleCons()

    rule "E-builtin-write":
      where `array`(*val_2), C_1.output
      let C_2 = C_1 + C(output: `array`(...val_2, ...val_1))
      conclusion C_1, Call("write", `array`(*val_1)), C_2, TupleCons()

    rule "E-builtin-writeErr":
      where `array`(*val_2), C_1.errOutput
      where C_2, C_1 + C(errOutput: `array`(...val_2, ...val_1))
      conclusion C_1, Call("writeErr", val_1), C_2, TupleCons()

  inductive step(inp C, inp e, out C, out e), "$1; $2 \\rightarrow $3; $4":
    rule "E-reduce-pure":
      premise pReducesTo(e_1, e_2)
      conclusion C_1, E_1[e_1], C_1, E_1[e_2]

    rule "E-reduce-impure":
      premise reducesTo(C_1, e_1, C_2, e_2)
      conclusion C_1, E_1[e_1], C_2, E_1[e_2]

    rule "E-tuple-loc-access":
      let val_1 = C_1.locs(z_1)
      conclusion C_1, E_1[L_1[FieldAccess(z_1, n_1)]], C_1, E_1[L_1[FieldAccess(val_1, n_1)]]
    rule "E-at-loc":
      let val_1 = C_1.locs(z_1)
      conclusion C_1, E_1[L_1[At(z_1, n_1)]], C_1, E_1[L_1[At(val_1, n_1)]]

    rule "E-return":
      let val_2 = copy(C_1, val_1)
      conclusion C_1, B_1[Frame(typ, E_1[Return(val_1)])], C_1, B_1[val_2]
    rule "E-return-unit":
      conclusion C_1, B_1[Frame(typ, E_1[Return()])], C_1, B_1[TupleCons()]

    rule "E-unreachable":
      condition B_1 != ()
      conclusion C_1, B_1[Unreachable()], C_1, Unreachable()

    # XXX: theorem support is not implemented...
    #[
    theorem e_1 of typ_1 and step(_, e_1, _, e_2), e_2 of typ_1
    # ^^ preservation. That is, reducing an expression doesn't change its type
    # XXX: the theorem doesn't consider subtyping

    theorem e_1 of typ_1, e_1 is val or step(_, e_1, _, e_2)
    # ^^ progress. That is, a valid expression is either an irreducible value,
    # or it must be reducible
    ]#
