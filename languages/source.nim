## Provides a reference implementation of the source language, written using
## Phy's meta-language. The formal definition is derived from the reference
## implementation.
##
## This is the one and only authoritative definition of the source language.
##
## As with most language-related things, the reference implementation /
## definition is a **work in progress**.
##
## **Important:** as is, the language definition **does not** match
## the originally intended semantics. This'll be fixed eventually.

import
  spec/[langdefs]

const lang* = language:
  alias n, z
  # TODO: remove `n` and use `z` directly. `n` usually refers to *natural*
  #       numbers, not *integer* numbers
  typ ident: Ident(string)
  alias x, ident
  typ expr:
    Ident(string)
    IntVal(z)
    FloatVal(r)
    TupleCons(*expr)
    Seq(texpr, *expr)
    Seq(StringVal(string))
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
    True
    False
    char(z) # UTF-8 byte
    loc(z) # first-class location
    `array`(*val)
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
    # A value is an irreducible expression.
    IntVal(n)
    FloatVal(z)
    True
    False
    char(z)
    loc(z)
    `array`(*val)
    `tuple`(+val)
    `proc`(typ, *[x, typ], e)

  subtype le, e:
    # Lvalue expression with all non-lvalue operands already evaluated.
    loc(z)
    FieldAccess(le, IntVal(n))
    At(le, IntVal(n))

  function desugar, expr -> e:
    # FIXME: the sub-expressions need to be desugared too!
    case _
    of And(expr_1, expr_2):
      If(expr_1, expr_2, Ident("false"))
    of Or(expr_1, expr_2):
      If(expr_1, Ident("true"), expr_2)
    of Decl(x_1, expr_1):
      Let(x_1, expr_1, TupleCons())
    of Exprs(*expr_1, Decl(x_1, expr_2), +expr_3):
      Exprs(...expr_1, Let(x_1, expr_2, Exprs(...expr_3)))
    of If(expr_1, expr_2):
      If(expr_1, expr_2, TupleCons())
    of If(Exprs(*expr_1, expr_2), expr_3, expr_4):
      Exprs(...expr_1, If(expr_2, expr_3, expr_4))
    of expr_1:
      expr_1

  ## Type Relations
  ## --------------

  inductive `<:`(inp typ, inp typ):
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
      conclusion typ_1, UnionTy(+typ_2)

  function `==`, (typ, typ) -> bool:
    ## Except for union types, all type equality uses *structural equality*.
    case _
    of UnionTy(+typ_1), UnionTy(+typ_2):
      if (for typ_3 in typ_1: contains(typ_2, typ_3)):
        if (for typ_3 in typ_2: contains(typ_1, typ_3)):
          true
        else:
          false
      else:
        false
    of typ_1, typ_2:
      same(typ_1, typ_2) # same structure, equal type

  function `!=`, (typ, typ) -> bool:
    case _
    of typ_1, typ_2:
      not(typ_1 == typ_2)

  inductive `<:=`(inp typ, inp typ):
    ## :math:`<:=` is the "sub or equal type" operator.
    rule "equal":
      condition typ_1 == typ_2
      conclusion typ_1, typ_2
    rule "subtype":
      condition typ_1 <: typ_2
      conclusion typ_1, typ_2

  ## Typing Judgment
  ## ---------------
  ##
  ## The language's static semantics consist of typing judgements, relating a
  ## symbol context and abstract syntax expression to a type.

  record C, (symbols: (string -> typ), ret: typ)
  ## :math:`C` is the symbol environment.

  function common, (typ, typ) -> typ:
    ## Computes the closest common ancestor type for a type pair. The function
    ## is not total, as not all two types have a common ancestor type.
    case _
    of typ_1, typ_2:
      if typ_1 == typ_2:     typ_1
      else:
        if typ_1 <: typ_2:   typ_2
        else:
          if typ_2 <: typ_1: typ_1
          else:              fail # no common type

  inductive ttypes(inp C, inp texpr, out typ):
    axiom "S-void-type",        C, VoidTy(),  VoidTy()
    axiom "S-unit-type",        C, UnitTy(),  UnitTy()
    axiom "S-bool-type",        C, BoolTy(),  BoolTy()
    axiom "S-char-type",        C, CharTy(),  CharTy()
    axiom "S-int-type",         C, IntTy(),   IntTy()
    axiom "S-float-type",       C, FloatTy(), FloatTy()
    axiom "S-empty-tuple-type", C, TupleTy(), UnitTy()

    rule "S-type-ident":
      condition string_1 in C_1.symbols
      where type(typ_1), C_1.symbols(string_1)
      conclusion C_1, Ident(string_1), typ_1

    rule "S-tuple-type":
      premise ...ttypes(C_1, texpr_1, typ_1)
      condition ...(typ_1 != VoidTy())
      conclusion C_1, TupleTy(+texpr_1), TupleTy(...typ_1)

    rule "S-union-type":
      premise ...ttypes(C_1, texpr_1, typ_1)
      condition ...(typ_1 != VoidTy())
      condition uniqueTypes(typ_1) # there must be no duplicate types
      conclusion C_1, UnionTy(+texpr_1), UnionTy(...typ_1)

    rule "S-proc-type":
      premise ttypes(C_1, texpr_1, typ_1)
      premise ...ttypes(C_1, texpr_2, typ_2)
      condition ...(typ_2 != VoidTy())
      conclusion C_1, ProcTy(texpr_1, *texpr_2), ProcTy(typ_1, ...typ_2)

    rule "S-seq-type":
      premise ttypes(C_1, texpr_1, typ_1)
      condition typ_1 != VoidTy()
      conclusion C_1, SeqTy(texpr_1), SeqTy(typ_1)

  def builtIn,
    {"==", "<=", "<", "+", "-", "*", "div", "mod", "true", "false", "write",
     "writeErr", "readFile"}

  function stripMut, typ -> typ:
    case _
    of mut(typ_1): typ_1
    of typ_1:      typ_1

  inductive mtypes(inp C, inp e, out typ):
    # relates an expression to its non-mut-qualified type
    rule "":
      premise types(C_1, e_1, typ_1)
      conclusion C_1, e_1, stripMut(typ_1)

  function isType, typ -> bool:
    case _
    of type(typ): true
    of typ:       false

  inductive types(inp C, inp e, out typ):
    axiom "S-int",   C, IntVal(n), IntTy()
    axiom "S-float", C, FloatVal(r), FloatTy()
    axiom "S-false", C, Ident("false"), BoolTy()
    axiom "S-true",  C, Ident("true"), BoolTy()
    axiom "S-unit",  C, TupleCons(), UnitTy()
    axiom "S-unreachable", C, Unreachable(), VoidTy()

    rule "S-identifier":
      condition string_1 in C_1.symbols
      let typ_1 = C_1.symbols(string_1)
      # TODO: split symbols into two maps, one for value and one for type
      #       identifiers, which would allow getting rid of the `type` modifier
      condition not isType(typ_1) # normal identifiers don't bind types
      conclusion C_1, Ident(string_1), typ_1

    rule "S-tuple":
      premise ...mtypes(C_1, e_1, typ_1)
      condition ...(typ_1 != VoidTy())
      conclusion C_1, TupleCons(+e_1), TupleTy(...typ_1)

    rule "S-seq-cons":
      premise ttypes(C_1, texpr_1, typ_1)
      premise ...types(C_1, e_2, typ_2)
      condition ...(typ_2 <:= typ_1)
      conclusion C_1, Seq(texpr_1, *e_2), SeqTy(typ_1)

    axiom "S-string-cons", C, Seq(StringVal(string)), SeqTy(CharTy())

    rule "S-return":
      premise mtypes(C_1, e_1, typ_1)
      condition typ_1 <:= C_1.ret
      conclusion C_1, Return(e_1), VoidTy()

    rule "S-return-unit":
      condition C_1.ret == UnitTy()
      conclusion C_1, Return(), VoidTy()

    rule "S-field":
      premise types(C_1, e_1, typ_1)
      where TupleTy(+typ_3), typ_1
      where typ_2, typ_3[n_1]
      conclusion C_1, FieldAccess(e_1, IntVal(n_1)), typ_2

    rule "S-mut-field":
      premise types(C_1, e_1, mut(typ_1))
      where TupleTy(+typ_3), typ_1
      where typ_2, typ_3[n_1]
      conclusion C_1, FieldAccess(e_1, IntVal(n_1)), mut(typ_2)

    rule "S-at":
      premise types(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, IntTy())
      where SeqTy(typ_2), typ_1
      conclusion C_1, At(e_1, e_2), typ_2

    rule "S-mut-at":
      premise types(C_1, e_1, mut(typ_1))
      premise mtypes(C_1, e_2, IntTy())
      where SeqTy(typ_2), typ_1
      conclusion C_1, At(e_1, e_2), mut(typ_2)

    rule "S-asgn":
      premise types(C_1, e_1, mut(typ_1))
      premise mtypes(C_1, e_2, typ_2)
      condition typ_2 <:= typ_1
      conclusion C_1, Asgn(e_1, e_2), UnitTy()

    rule "S-let":
      condition string_1 notin C_1.symbols
      condition string_1 notin builtIn
      premise mtypes(C_1, e_1, typ_1)
      let C_2 = C_1 + C(symbols: {string_1: mut(typ_1)})
      premise mtypes(C_2, e_2, typ_2)
      conclusion C_1, Let(Ident(string_1), e_1, e_2), typ_2

    rule "S-exprs":
      premise ...mtypes(C_1, e_1, UnitTy())
      premise types(C_1, e_2, typ_2)
      conclusion C_1, Exprs(*e_1, e_2), typ_2

    rule "S-void-short-circuit":
      # if any expression in the list is of type void, so is the list itself
      premise ...mtypes(C_1, e_1, typ_3)
      condition ...(typ_3 in {VoidTy(), UnitTy()})
      condition VoidTy() in typ_3
      premise types(C_1, e_2, typ)
      conclusion C_1, Exprs(*e_1, e_2), VoidTy()

    rule "S-if":
      premise mtypes(C_1, e_1, BoolTy())
      premise mtypes(C_1, e_2, typ_1)
      premise mtypes(C_1, e_3, typ_2)
      let typ_3 = common(typ_1, typ_2)
      conclusion C_1, If(e_1, e_2, e_3), typ_3

    rule "S-while":
      premise mtypes(C_1, e_1, BoolTy())
      premise mtypes(C_1, e_2, typ_1)
      condition typ_1 in {VoidTy(), UnitTy()}
      conclusion C_1, While(e_1, e_2), UnitTy()

    rule "S-while":
      premise mtypes(C_1, e_1, typ_1)
      condition typ_1 in {VoidTy(), UnitTy()}
      conclusion C_1, While(True, e_1), VoidTy()

    rule "S-builtin-not":
      premise mtypes(C_1, e_1, typ_1)
      condition typ_1 == BoolTy()
      conclusion C_1, Call(Ident("not"), e_1), BoolTy()

    rule "S-builtin-plus":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call(Ident("+"), e_1, e_2), typ_1

    rule "S-builtin-minus":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call(Ident("-"), e_1, e_2), typ_1

    rule "S-builtin-mul":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 == IntTy()
      conclusion C_1, Call(Ident("*"), e_1, e_2), typ_1

    rule "S-builtin-div":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 == IntTy()
      conclusion C_1, Call(Ident("div"), e_1, e_2), typ_1

    rule "S-builtin-eq":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 in {BoolTy(), IntTy(), FloatTy()}
      conclusion C_1, Call(Ident("=="), e_1, e_2), BoolTy()

    rule "S-builtin-lt":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call(Ident("<"), e_1, e_2), BoolTy()

    rule "S-builtin-le":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call(Ident("<="), e_1, e_2), BoolTy()

    rule "S-builtin-mod":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 == IntTy()
      conclusion C_1, Call(Ident("mod"), e_1, e_2), typ_1

    rule "S-builtin-len":
      premise mtypes(C_1, e_1, SeqTy(typ))
      conclusion C_1, Call(Ident("len"), e_1), IntTy()

    rule "S-builtin-concat":
      premise mtypes(C_1, e_1, SeqTy(typ_1))
      premise mtypes(C_1, e_2, typ_2)
      condition typ_2 <:= typ_1
      conclusion C_1, Call(Ident("concat"), e_1, e_2), UnitTy()

    rule "S-builtin-write":
      premise mtypes(C_1, e_1, SeqTy(CharTy()))
      conclusion C_1, Call(Ident("write"), e_1), UnitTy()

    rule "S-builtin-writeErr":
      premise mtypes(C_1, e_1, SeqTy(CharTy()))
      conclusion C_1, Call(Ident("writeErr"), e_1), UnitTy()

    rule "S-builtin-readFile":
      premise mtypes(C_1, e_1, SeqTy(CharTy()))
      conclusion C_1, Call(Ident("readFile"), e_1), SeqTy(CharTy())

    rule "S-call":
      premise mtypes(C_1, e_1, typ_1)
      where ProcTy(typ_r, *typ_p), typ_1
      premise ...mtypes(C_1, e_2, typ_a)
      condition ...(typ_a <:= typ_p)
      conclusion C_1, Call(e_1, *e_2), typ_r

    rule "S-Frame":
      premise types(C_1, e_1, typ_2)
      condition typ_2 <:= typ_1
      conclusion C_1, Frame(typ_1, e_1), typ_1

    rule "S-proc-val":
      conclusion C_1, `proc`(typ_r, *[x, typ_p], e), ProcTy(typ_r, ...typ_p)

    rule "S-seq-with":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_3)
      where SeqTy(typ_2), typ_1
      condition typ_3 <:= typ_2
      conclusion C_1, With(e_1, n_1, e_2), typ_1

    rule "S-tuple-with":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      where TupleTy(+typ_4), typ_1
      where typ_3, typ_4[n_1]
      condition typ_2 <:= typ_3
      conclusion C_1, With(e_1, n_1, e_2), typ_3

  inductive toplevel(inp C, inp (decl + module), out C):
    rule "S-type-decl":
      premise ttypes(C_1, texpr_1, typ_1)
      where C_2, C_1 + C(symbols: {string_1: type(typ_1)})
      conclusion C_1, TypeDecl(Ident(string_1), texpr_1), C_2

    rule "S-proc-decl":
      condition string_1 notin C_1.symbols
      condition unique(string_2) # all symbols must be unique
      condition string_1 notin string_2
      premise ttypes(C_1, texpr_1, typ_1)
      premise ...ttypes(C_1, texpr_2, typ_2)
      condition ...(typ_2 != VoidTy())
      let typ_3 = ProcTy(typ_1, ...typ_2)
      let C_2 = C_1 + C(symbols: {string_1: typ_3})
      let C_3 = C_2 + C(ret: typ_1, symbols: map(zip(string_2, typ_2)))
      premise types(C_3, e_1, VoidTy())
      conclusion C_1, ProcDecl(Ident(string_1), texpr_1, Params(*ParamDecl(Ident(string_2), texpr_2)), e_1), C_2

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

  function substitute, (e, (string -> e)) -> e:
    ## The substitution function, which handles binding values/expressions to
    ## identifiers. Identifiers cannot be shadowed.
    case _
    of Exprs(+e_1), any_1:
      Exprs(...(substitute(e_1, any_1)))
    of Let(ident_1, e_1, e_2), any_1:
      Let(ident_1, substitute(e_1, any_1), substitute(e_2, any_1))
    of If(e_1, e_2, e_3), any_1:
      If(substitute(e_1, any_1), substitute(e_2, any_1), substitute(e_3, any_1))
    of Call(+e_1), any_1:
      Call(...substitute(e_1, any_1))
    of Asgn(e_1, e_2), any_1:
      Asgn(substitute(e_1, any_1), substitute(e_2, any_1))
    of TupleCons(*e_1), any_1:
      TupleCons(...substitute(e_1, any_1))
    of Seq(texpr, *e_1), any_1:
      Seq(texpr, ...substitute(e_1, any_1))
    of FieldAccess(e_1, IntVal(z_1)), any_1:
      FieldAccess(substitute(e_1, any_1), IntVal(z_1))
    of At(e_1, e_2), any_1:
      At(substitute(e_1, any_1), substitute(e_2, any_1))
    of While(e_1, e_2), any_1:
      While(substitute(e_1, any_1), substitute(e_2, any_1))
    of Return(e_1), any_1:
      Return(substitute(e_1, any_1))
    of Ident(string_1), any_1:
      # the actual substitution
      if string_1 in any_1:
        any_1(string_1)
      else:
        Ident(string_1)
    of e_1, _:
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
      if same(n_1, (-2 ^ 63)):
        if same(n_2, -1):
          fail
        else:
          trunc(n_1 / n_2)
      else:
        trunc(n_1 / n_2)

  function intMod, (n, n) -> n:
    case _
    of n_1, 0: fail
    of n_1, n_2: n_1 - (n_2 * trunc(n_1 / n_2))

  function floatAdd, (r, r) -> r:
    ## XXX: not defined
  function floatSub, (r, r) -> r:
    ## XXX: not defined

  function valEq, (val, val) -> val:
    case _
    of val_1, val_2:
      if same(val_1, val_2):
        True
      else:
        False

  function lt, (val, val) -> val:
    case _
    of IntVal(n_1), IntVal(n_2):
      if n_1 < n_2: True
      else:         False
    of FloatVal(r_1), FloatVal(r_2):
      if r_1 < r_2: True
      else:         False

  function lessEqual, (val, val) -> val:
    case _
    of val_1, val_2:
      if same(valEq(val_1, val_2), True):
        True
      else:
        lt(val_1, val_2)

  # TODO: the floating-point operations need to be defined according to the
  #       IEEE 754.2008 standard

  record DC, {locs: (z -> val),
              nloc: z,
              time: z,
              output: val,
              errOutput: val,
              files: ((string, z) -> val)} # name + time -> content
  ## `DC` is the dynamic context

  function copy, (DC, val) -> val:
    ## The `copy` function takes a context and value and maps them to a value
    ## that is neither a location nor contains any.
    case _
    of DC_1, loc(z_1): copy(DC_1, DC_1.locs(z_1))
    of DC, val_1:      val_1

  function utf8Bytes, string -> *z:
    # TODO: the function is mostly self-explanatory, but it should be defined in
    #       a bit more detail nonetheless
    ##

  ## Evaluation Contexts
  ## ~~~~~~~~~~~~~~~~~~~

  context Etick:
    FieldAccess(Etick, IntVal(n))
    At(Etick, e)
    At(le, E)

  context L:
    # evaluation context for lvalues
    hole
    FieldAccess(L, IntVal(n))
    At(L, IntVal(n))
  context E:
    hole
    Exprs(E, *e)
    FieldAccess(E, IntVal(n))
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
    E
    #E[B]
    # FIXME: not allowed according to the new rules. Needs a workaround...
    Frame(typ, B)

  ## Reductions and Steps
  ## ~~~~~~~~~~~~~~~~~~~~

  inductive pReducesTo(inp e, out e):
    # pure reductions, that is, reductions not dependent on the execution
    # context
    axiom "E-false", Ident("false"), False
    axiom "E-true",  Ident("true"),  True
    axiom "E-exprs-fold", Exprs(val_1), val_1
    axiom "E-exprs", Exprs(TupleCons(), +e_1), Exprs(...e_1)
    axiom "E-if-true", If(True, e_1, e_2), e_1
    axiom "E-if-false", If(False, e_1, e_2), e_2

    axiom "E-while", While(e_1, e_2), If(e_1, Exprs(e_2, While(e_1, e_2)), TupleCons())

    rule "E-tuple-access":
      where `tuple`(+val_3), val_1
      where val_2, val_3[n_1]
      conclusion FieldAccess(val_1, IntVal(n_1)), val_2

    axiom "E-field-asgn", Asgn(FieldAccess(le_1, IntVal(n_1)), val_1), Asgn(le_1, With(le_1, n_1, val_1))
    axiom "E-elem-asgn", Asgn(At(le_1, IntVal(n_1)), val_1), Asgn(le_1, With(le_1, n_1, val_1))

    rule "E-at":
      condition 0 <= n_1
      condition n_1 < len(val_1)
      let val_2 = val_1[n_1]
      conclusion At(array(*val_1), IntVal(n_1)), val_2

    rule "E-at-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion At(array(*val_1), IntVal(n_1)), Unreachable()

    rule "E-with-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion With(array(*val_1), n_1, val_2), Unreachable()

    axiom "E-not-false", Call(Ident("not"), False), True
    axiom "E-not-true",  Call(Ident("not"), True),  False

    rule "E-add-int":
      let n_3 = intAdd(n_1, n_2)
      conclusion Call(Ident("+"), IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-add-int-overflow":
      condition (n_1, n_2) notin intAdd(n_1, n_2)
      conclusion Call(Ident("+"), IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-sub-int":
      let n_3 = intSub(n_1, n_2)
      conclusion Call(Ident("-"), IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-sub-int-overflow":
      condition (n_1, n_2) notin intSub(n_1, n_2)
      conclusion Call(Ident("-"), IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-mul-int":
      let n_3 = intMul(n_1, n_2)
      conclusion Call(Ident("*"), IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-mul-int-overflow":
      condition (n_1, n_2) notin intMul
      conclusion Call(Ident("*"), IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-div-int":
      let n_3 = intDiv(n_1, n_2)
      conclusion Call(Ident("div"), IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-div-int-overflow":
      condition (n_1, n_2) notin intDiv
      conclusion Call(Ident("div"), IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-mod-int":
      let n_3 = intDiv(n_1, n_2)
      conclusion Call(Ident("div"), IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-mod-int-overflow":
      condition (n_1, n_2) notin intDiv
      conclusion Call(Ident("div"), IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-add-float":
      let r_3 = floatAdd(r_1, r_2)
      conclusion Call(Ident("+"), FloatVal(r_1), FloatVal(r_2)), FloatVal(r_3)
    rule "E-sub-float":
      let r_3 = floatSub(r_1, r_2)
      conclusion Call(Ident("-"), FloatVal(r_1), FloatVal(r_2)), FloatVal(r_3)

    rule "E-builtin-eq":
      let val_3 = valEq(val_1, val_2)
      conclusion Call(Ident("=="), val_1, val_2), val_3
    rule "E-builtin-le":
      let val_3 = lessEqual(val_1, val_2)
      conclusion Call(Ident("<="), val_1, val_2), val_3
    rule "E-builtin-lt":
      let val_3 = lt(val_1, val_2)
      conclusion Call(Ident("<"), val_1, val_2), val_3

    rule "E-builtin-len":
      let n_1 = len(val_1)
      conclusion Call(Ident("len"), array(*val_1)), IntVal(n_1)

    rule "E-builtin-concat":
      conclusion Call(Ident("concat"), `array`(*val_1), val_2), `array`(...val_1, val_2)

    rule "E-call-reduce":
      # the call is replaced with the procedure's body (in which all
      # occurrences of the parameters were substituted with a copy of the
      # respective argument), which is wrapped in a `Frame` tree
      where `proc`(typ_r, *[Ident(string_1), typ_p], e_1), val_1
      where e_2, substitute(e_1, map(zip(string_1, val_2)))
      conclusion Call(val_1, *val_2), Frame(typ_r, e_2)

  inductive reducesTo(inp DC, inp e, out DC, out e):
    rule "E-tuple-cons":
      where +val_2, ...copy(DC_1, val_1)
      conclusion DC_1, TupleCons(+val_1), DC_1, `tuple`(...val_2)

    rule "E-seq-cons":
      where +val_2, ...copy(DC_1, val_1)
      conclusion DC_1, Seq(typ, *val_1), DC_1, `array`(...val_2)

    rule "E-string-cons":
      # FIXME: doesn't need to be an impure reduction
      where *z_1, utf8Bytes(string_1)
      conclusion DC_1, Seq(StringVal(string_1)), DC_1, array(...IntVal(z_1))

    rule "E-let-introduce":
      let z_1 = DC_1.nloc
      let val_2 = copy(DC_1, val_1)
      let DC_2 = DC_1 + DC(locs: {z_1 : val_2}, nloc: z_1 + 1)
      let e_2 = substitute(e_1, {string_1: loc(z_1)})
      conclusion DC_1, Let(Ident(string_1), val_1, e_1), DC_2, e_2
    # TODO: the location needs to be removed from the execution context once
    #       `e_2` is reduced to a value, otherwise it remains accessible. This
    #       is not a problem at the moment, but it will be once there are
    #       first-class locations (e.g., pointers) in the source language.
    #       Removing the location from the store could be achieved via a new
    #       `(Pop x)` construct, where `(Let x val e)` reduces to `(Pop x e)`

    rule "E-with-array":
      let val_3 = val_1[n_1]
      # FIXME: this is wrong. The n-th element of the array must be replaced
      #        with val_2
      conclusion DC_1, With(array(*val_1), n_1, val_2), DC_1, val_3
    rule "E-with-tuple":
      let val_3 = val_1[n_1]
      # FIXME: same here
      conclusion DC_1, With(`tuple`(+val_1), n_1, val_2), DC_1, val_3

    rule "E-asgn":
      let DC_2 = DC_1 + DC(locs: {z_1 : val_1})
      conclusion DC_1, Asgn(loc(z_1), val_1), DC_2, TupleCons()

    rule "E-builtin-write":
      where `array`(*val_2), DC_1.output
      let DC_2 = DC_1 + DC(output: array(...val_2, ...val_1))
      conclusion DC_1, Call(Ident("write"), array(*val_1)), DC_2, TupleCons()

    rule "E-builtin-writeErr":
      where `array`(*val_2), DC_1.errOutput
      where DC_2, DC_1 + DC(errOutput: array(...val_2, ...val_1))
      conclusion DC_1, Call(Ident("writeErr"), array(*val_1)), DC_2, TupleCons()

    rule "E-builtin-readFile":
      # the extra time parameter is used to model the fact that the file
      # access doesn't always yield the same result, even when the program
      # does nothing
      where val_2, DC_1.files(z_1, DC_1.time)
      where `array`(*char(z)), val_2
      where n_1, DC_1.time + 1
      where DC_2, DC_1 + DC(time: n_1)
      conclusion DC_1, Call(Ident("readFile"), array(*char(z_1))), DC_2, val_2

  inductive step(inp DC, inp e, out DC, out e):
    rule "E-reduce-pure":
      premise pReducesTo(e_1, e_2)
      conclusion DC_1, E_1[e_1], DC_1, E_1[e_2]

    rule "E-reduce-impure":
      premise reducesTo(DC_1, e_1, DC_2, e_2)
      conclusion DC_1, E_1[e_1], DC_2, E_1[e_2]

    rule "E-tuple-loc-access":
      let val_1 = DC_1.locs(z_1)
      conclusion DC_1, E_1[L_1[FieldAccess(loc(z_1), IntVal(n_1))]], DC_1, E_1[L_1[FieldAccess(val_1, IntVal(n_1))]]
    rule "E-at-loc":
      let val_1 = DC_1.locs(z_1)
      conclusion DC_1, E_1[L_1[At(loc(z_1), IntVal(n_1))]], DC_1, E_1[L_1[At(val_1, IntVal(n_1))]]

    rule "E-return":
      let val_2 = copy(DC_1, val_1)
      conclusion DC_1, B_1[Frame(typ, E_1[Return(val_1)])], DC_1, B_1[val_2]
    rule "E-return-unit":
      conclusion DC_1, B_1[Frame(typ, E_1[Return()])], DC_1, B_1[TupleCons()]

    rule "E-unreachable":
      conclusion DC_1, B_1[Unreachable()], DC_1, Unreachable()

    # XXX: theorem support is not implemented...
    #[
    theorem e_1 of typ_1 and step(_, e_1, _, e_2), e_2 of typ_1
    # ^^ preservation. That is, reducing an expression doesn't change its type
    # XXX: the theorem doesn't consider subtyping

    theorem e_1 of typ_1, e_1 is val or step(_, e_1, _, e_2)
    # ^^ progress. That is, a valid expression is either an irreducible value,
    # or it must be reducible
    ]#

  inductive cstep(inp DC, inp e, out DC, out e):
    ## Transitive closure of `step`. Relates an expression to the irreducible
    ## expression it reduces to (if any).
    axiom "value", DC_1, val_1, DC_1, val_1
    axiom "unreachable", DC_1, Unreachable(), DC_1, Unreachable()
    rule "reducible":
      premise step(DC_1, e_1, DC_2, e_2)
      premise cstep(DC_2, e_2, DC_3, e_3)
      conclusion DC_1, e_1, DC_3, e_3

  # ------------
  # boilerplate functions that should rather not exist

  function `not`, bool -> bool:
    case _
    of true: false
    of false: true

  # XXX: the built-in `in` function should consider the custom equality
  #      operator, which would render `contains` obsolete
  function contains, (*typ, typ) -> bool:
    case _
    of [typ_1, *typ_2], typ_3:
      if typ_1 == typ_3:
        true
      else:
        contains(typ_2, typ_3)
    of _:
      false

  function uniqueTypes, *typ -> bool:
    ## Computes whether all types in the list are unique.
    case _
    of [typ_1, +typ_2]:
      if not contains(typ_2, typ_1):
        uniqueTypes(typ_2)
      else:
        false
    of _:
      true

  function unique, *string -> bool:
    ## Computes whether all strings in the list are unique.
    case _
    of [string_1, +string_2]:
      if string_1 notin string_2:
        unique(string_2)
      else:
        false
    of _:
      true
