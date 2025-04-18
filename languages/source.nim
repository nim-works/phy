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

  typ equality:
    Gt
    Lt
    Eq

  typ option:
    None
    Some(equality)

  typ float:
    # IEEE-754.2008 binary64 float representation (without signed nans and nan
    # payloads)
    Nan
    Inf(bool)
    Zero(bool)
    Finite(bool, n, z) # sign, significand, exponent

  typ ident: Ident(string)
  alias x, ident
  typ pattern:
    As(x, texpr)
  typ rule:
    Rule(pattern, expr)
  typ eindex:
    # element index
    IntVal(z)
    Ident(string)

  typ expr:
    Ident(string)
    IntVal(z)
    FloatVal(float)
    ArrayCons(+expr)
    TupleCons(*expr)
    RecordCons(+Field(ident, expr))
    Seq(texpr, *expr)
    Seq(StringVal(string))
    Call(+expr)
    FieldAccess(expr, eindex)
    At(expr, expr)
    As(expr, texpr)
    And(expr, expr)
    Or(expr, expr)
    If(expr, expr, expr)
    If(expr, expr)
    Match(expr, +rule)
    While(expr, expr)
    Return(expr)
    Return()
    Unreachable()
    Exprs(+expr)
    Asgn(expr, expr)
    Decl(ident, expr)

    Let(ident, expr, expr)
    Letrec(ident, expr, expr)

    # syntax not available at the source level:
    True
    False
    char(z) # UTF-8 byte
    loc(z) # first-class location
    `array`(*val)
    # TODO: ^^ use the `Seq` constructor instead; it also preserves the type
    `proc`(typ, *[x, typ], e)

    With(e, n, e) # return a tuple/array value with the n-th element replaced
    With(e, string, e)
    Frame(typ, e) # a special expression for assisting with evaluation

  alias e, expr

  typ fieldDecl: Field(ident, texpr)
  typ texpr:
    Ident(string)
    VoidTy()
    UnitTy()
    BoolTy()
    CharTy()
    IntTy()
    FloatTy()
    ArrayTy(IntVal(z), texpr)
    TupleTy(*texpr)
    UnionTy(+texpr)
    ProcTy(+texpr)
    SeqTy(texpr)
    RecordTy(+fieldDecl)

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
    FloatVal(float)
    True
    False
    char(z)
    `array`(*val) # TODO: make this a seq
    ArrayCons(+val)
    TupleCons(*val) # an empty tuple is also a valid value (i.e., unit)
    RecordCons(+Field(x, val))
    `proc`(typ, *[x, typ], e)

  subtype le, e:
    # Lvalue expression with all non-lvalue operands already evaluated.
    loc(z)
    FieldAccess(le, eindex)
    At(le, IntVal(n))

  func update(a: expr, xfrm: e -> e) -> expr =
    ## Transforms and replaces all sub-expressions in `a` using the given
    ## function.
    case a
    of Exprs(+e_1):
      Exprs(...xfrm(e_1))
    of Let(ident_1, e_1, e_2):
      Let(ident_1, xfrm(e_1), xfrm(e_2))
    of Decl(ident_1, e_1):
      Decl(ident_1, xfrm(e_1))
    of If(e_1, e_2, e_3):
      If(xfrm(e_1), xfrm(e_2), xfrm(e_3))
    of Match(e_1, +Rule(As(x_1, texpr_1), e_2)):
      Match(xfrm(e_1), ...Rule(As(x_1, texpr_1), xfrm(e_2)))
    of Call(+e_1):
      Call(...xfrm(e_1))
    of Asgn(e_1, e_2):
      Asgn(xfrm(e_1), xfrm(e_2))
    of ArrayCons(+e_1):
      ArrayCons(...e_1)
    of TupleCons(*e_1):
      TupleCons(...xfrm(e_1))
    of RecordCons(+Field(x_1, e_1)):
      RecordCons(...Field(x_1, xfrm(e_1)))
    of Seq(texpr_1, *e_1):
      Seq(texpr_1, ...xfrm(e_1))
    of FieldAccess(e_1, eindex_1):
      FieldAccess(xfrm(e_1), eindex_1)
    of At(e_1, e_2):
      At(xfrm(e_1), xfrm(e_2))
    of As(e_1, texpr_1):
      As(xfrm(e_1), texpr_1)
    of While(e_1, e_2):
      While(xfrm(e_1), xfrm(e_2))
    of Return(e_1):
      Return(xfrm(e_1))
    of e_1:
      e_1

  func up(a: expr) -> expr =
    ## Moves exprs lists "upwards".
    case a
    of If(Exprs(*e_1, e_2), e_3, e_4):
      # re-apply until there's no more exprs in the If's condition position
      Exprs(...e_1, up(If(e_2, e_3, e_4)))
    of e_1:
      e_1

  func expand(a: expr) -> expr =
    ## Expands all non-Decl syntax sugar.
    case a
    of And(e_1, e_2):
      expand(If(e_1, e_2, Ident("false")))
    of Or(e_1, e_2):
      expand(If(e_1, Ident("true"), e_2))
    of If(e_1, e_2):
      expand(If(e_1, e_2, TupleCons()))
    of If(e_1, e_2, e_3):
      up(update(If(e_1, e_2, e_3), expand))
    of e_1:
      update(e_1, expand)

  func declToLet(a: expr) -> expr =
    ## Transforms `Decl` into `Let`.
    case a
    of Decl(x_1, e_1):
      # a trailing decl
      Let(x_1, declToLet(e_1), TupleCons())
    of Exprs(*e_1, Decl(x_1, e_2), +e_3):
      # this only transforms the trailing decl, but there might be more than
      # one decl in the list, hence the recursion
      declToLet(Exprs(...e_1, Let(x_1, e_2, Exprs(...e_3))))
    of e_1:
      update(e_1, declToLet)

  func desugarExpr(a: expr) -> expr =
    # first expand all sugar, then transform all decls
    declToLet(expand(a))

  func desugarDecl(d: decl) -> decl =
    case d
    of ProcDecl(x_1, texpr_1, Params(*paramDecl_1), e_1):
      ProcDecl(x_1, texpr_1, Params(...paramDecl_1), desugarExpr(e_1))
    of TypeDecl(x_1, texpr_1):
      TypeDecl(x_1, texpr_1)

  func desugar(a: module+decl+expr) -> module+decl+expr =
    case a
    of e_1:
      desugarExpr(e_1)
    of decl_1:
      Module(desugarDecl(decl_1))
    of Module(*decl_1):
      Module(...desugarDecl(decl_1))

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

  func `==`(a, b: typ) -> bool =
    ## Type equality.
    case (a, b)
    of UnionTy(+typ_1), UnionTy(+typ_2):
      # equal set of types -> equivalent types
      identical(typ_1, typ_2)
    of RecordTy(+Field(Ident(string_1), typ_1)),
       RecordTy(+Field(Ident(string_2), typ_2)):
      # equal fields -> equivalent type
      let m_1 = zip(string_1, typ_1)
      let m_2 = zip(string_2, typ_2)
      if (for it in m_1: mapContains(m_2, it)):
        if (for it in m_2: mapContains(m_1, it)):
          true
        else:
          false
      else:
        false
    of ArrayTy(IntVal(z_1), typ_1), ArrayTy(IntVal(z_2), typ_2):
      same(z_1, z_2) and typ_1 == typ_2
    else:
      same(a, b) # same structure -> equivalent type

  func `!=`(a, b: typ) -> bool = not(a == b)

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

  func common(a, b: typ) -> typ =
    ## Computes the closest common ancestor type for a type pair. The function
    ## is not total, as not all two types have a common ancestor type.
    if a == b:     a
    else:
      if a <: b:   b
      else:
        if b <: a: a
        else:      fail # no common type

  func commonAll(list: *typ) -> typ =
    ## Computes the closest common ancestor of all types in the list, or
    ## fails, if there's no such type.
    case list
    of [typ_1, typ_2, +typ_3]:
      common(common(typ_1, typ_2), commonAll(typ_3))
    of [typ_1, typ_2]:
      common(typ_1, typ_2)
    of [typ_1]:
      typ_1

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

    rule "S-array-type":
      premise ttypes(C_1, texpr_1, typ_1)
      condition typ_1 != VoidTy()
      condition 0 <= z_1 and z_1 <= (2 ^ 32) - 1
      conclusion C_1, ArrayTy(IntVal(z_1), texpr_1), ArrayTy(IntVal(z_1), typ_1)

    rule "S-tuple-type":
      premise ...ttypes(C_1, texpr_1, typ_1)
      condition ...(typ_1 != VoidTy())
      conclusion C_1, TupleTy(+texpr_1), TupleTy(...typ_1)

    rule "S-record-type":
      premise ...ttypes(C_1, texpr_1, typ_1)
      condition ...(typ_1 != VoidTy())
      condition unique(string_1)
      conclusion C_1, RecordTy(+Field(Ident(string_1), texpr_1)),
                      RecordTy(...Field(Ident(string_1), typ_1))

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
    {"==", "<=", "<", "+", "-", "*", "/", "div", "mod", "true", "false",
     "write", "writeErr", "readFile"}

  func stripMut(t: typ) -> typ =
    case t
    of mut(typ_1): typ_1
    of typ_1:      typ_1

  inductive mtypes(inp C, inp e, out typ):
    # relates an expression to its non-mut-qualified type
    rule "":
      premise types(C_1, e_1, typ_1)
      conclusion C_1, e_1, stripMut(typ_1)

  func isType(t: typ) -> bool =
    case t
    of type(typ): true
    of typ:       false

  func unionOfAux(list: *typ, accum: typ) -> typ =
    # `TupleTy` is used as the accumulator, because it can hold any number
    # of types
    case list
    of [typ_1, *typ_2]:
      if contains(typ_2, typ_1):
        # it's a duplicate; skip
        unionOfAux(typ_2, accum)
      else:
        case accum
        of TupleTy(*typ_3):
          unionOfAux(typ_2, TupleTy(...typ_3, typ_1))
    else:
      accum

  func unionOf(list: *typ) -> typ =
    case unionOfAux(list, TupleTy())
    of TupleTy(typ_1, +typ_2):
      UnionTy(typ_1, ...typ_2)
    of TupleTy(typ_1):
      typ_1

  inductive types(inp C, inp e, out typ):
    axiom "S-int",   C, IntVal(n), IntTy()
    axiom "S-float", C, FloatVal(float), FloatTy()
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

    rule "S-array":
      premise ...mtypes(C_1, e_1, typ_1)
      condition ...(typ_1 != VoidTy())
      condition len(e_1) <= (2 ^ 32) - 1
      let typ_2 = commonAll(typ_1)
      conclusion C_1, ArrayCons(+e_1), ArrayTy(IntVal(len(e_1)), typ_2)

    rule "S-tuple":
      premise ...mtypes(C_1, e_1, typ_1)
      condition ...(typ_1 != VoidTy())
      conclusion C_1, TupleCons(+e_1), TupleTy(...typ_1)

    rule "S-record":
      premise ...mtypes(C_1, e_1, typ_1)
      condition ...(typ_1 != VoidTy())
      condition unique(string_1)
      conclusion C_1, RecordCons(+Field(Ident(string_1), e_1)),
                      RecordTy(...Field(Ident(string_1), typ_1))

    rule "S-seq-cons":
      premise ttypes(C_1, texpr_1, typ_1)
      condition typ_1 != VoidTy()
      premise ...mtypes(C_1, e_2, typ_2)
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

    rule "S-rec-field":
      premise types(C_1, e_1, typ_1)
      where RecordTy(+Field(Ident(string_2), typ_2)), typ_1
      where typ_3, map(zip(string_2, typ_2))(string_1)
      conclusion C_1, FieldAccess(e_1, Ident(string_1)), typ_3

    rule "S-mut-rec-field":
      premise types(C_1, e_1, mut(typ_1))
      where RecordTy(+Field(Ident(string_2), typ_2)), typ_1
      where typ_3, map(zip(string_2, typ_2))(string_1)
      conclusion C_1, FieldAccess(e_1, Ident(string_1)), mut(typ_3)

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

    rule "S-at-array":
      premise types(C_1, e_1, ArrayTy(IntVal(z), typ_1))
      premise mtypes(C_1, e_2, IntTy())
      conclusion C_1, At(e_1, e_2), typ_1

    rule "S-mut-at-array":
      premise types(C_1, e_1, mut(ArrayTy(IntVal(z), typ_1)))
      premise mtypes(C_1, e_2, IntTy())
      conclusion C_1, At(e_1, e_2), mut(typ_1)

    rule "S-at-tuple":
      premise mtypes(C_1, e_1, TupleTy(+typ_2))
      premise mtypes(C_1, e_2, IntTy())
      conclusion C_1, At(e_1, e_2), unionOf(typ_2)

    rule "S-as":
      premise mtypes(C_1, e_1, typ_1)
      premise ttypes(C_1, texpr_1, typ_2)
      condition typ_2 != VoidTy()
      condition typ_1 <:= typ_2
      conclusion C_1, As(e_1, texpr_1), typ_2

    rule "S-asgn":
      premise types(C_1, e_1, mut(typ_1))
      premise mtypes(C_1, e_2, typ_2)
      condition typ_2 <:= typ_1
      conclusion C_1, Asgn(e_1, e_2), UnitTy()

    rule "S-let":
      condition string_1 notin C_1.symbols
      condition string_1 notin builtIn
      premise mtypes(C_1, e_1, typ_1)
      condition typ_1 != VoidTy()
      let C_2 = C_1 + C(symbols: {string_1: mut(typ_1)})
      premise mtypes(C_2, e_2, typ_2)
      conclusion C_1, Let(Ident(string_1), e_1, e_2), typ_2

    rule "S-letrec":
      condition string_1 notin C_1.symbols
      condition string_1 notin builtIn
      condition ...(string_2 notin C_1.symbols)
      condition ...(string_2 notin builtIn)
      premise ttypes(C_1, texpr_1, typ_1)
      premise ...ttypes(C_1, texpr_2, typ_2)
      let typ_3 = ProcTy(typ_1, ...typ_2)
      let C_2 = C_1 + C(symbols: {string_1: typ_3})
      let C_3 = C_2 + C(symbols: map(zip(string_2, typ_2)), ret: typ_1)
      # the procedure symbol is visible to the initializer expression
      premise mtypes(C_3, e_1, typ)
      premise mtypes(C_2, e_2, typ_4)
      conclusion C_1, Letrec(Ident(string_1), `proc`(texpr_1, *[Ident(string_2), texpr_2], e_1), e_2), typ_4

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

    rule "S-match":
      premise mtypes(C_1, e_1, typ_1)
      where UnionTy(+typ_2), typ_1
      premise ...ttypes(C_1, texpr_1, typ_3)
      condition uniqueTypes(typ_3)
      condition identical(typ_2, typ_3)
      condition ...(string_1 notin C_1.symbols)
      let C_2 = ...(C_1 + C(symbols: {string_1 : typ_3}))
      premise ...mtypes(C_2, e_2, typ_4)
      let typ_5 = commonAll(typ_4)
      conclusion C_1, Match(e_1, +Rule(As(Ident(string_1), texpr_1), e_2)), typ_5

    rule "S-while":
      premise mtypes(C_1, e_1, BoolTy())
      premise mtypes(C_1, e_2, typ_1)
      condition not same(e_1, Ident("true"))
      condition typ_1 in {VoidTy(), UnitTy()}
      conclusion C_1, While(e_1, e_2), UnitTy()

    rule "S-while-true":
      premise mtypes(C_1, e_1, typ_1)
      condition typ_1 in {VoidTy(), UnitTy()}
      conclusion C_1, While(Ident("true"), e_1), VoidTy()

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
      condition typ_1 in {IntTy(), FloatTy()}
      conclusion C_1, Call(Ident("*"), e_1, e_2), typ_1

    rule "S-builtin-float-div":
      premise mtypes(C_1, e_1, typ_1)
      premise mtypes(C_1, e_2, typ_2)
      condition typ_1 == typ_2
      condition typ_1 == FloatTy()
      conclusion C_1, Call(Ident("/"), e_1, e_2), typ_1

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
      conclusion C_1, Call(Ident("concat"), e_1, e_2), SeqTy(typ_1)

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

  inductive toplevel(inp C, inp (decl + module), out C, out typ):
    rule "S-type-decl":
      condition string_1 notin C_1.symbols
      condition string_1 notin builtIn
      premise ttypes(C_1, texpr_1, typ_1)
      where C_2, C_1 + C(symbols: {string_1: type(typ_1)})
      conclusion C_1, TypeDecl(Ident(string_1), texpr_1), C_2, VoidTy()

    rule "S-proc-decl":
      condition string_1 notin C_1.symbols
      condition string_1 notin builtIn
      condition ...(string_2 notin C_1.symbols)
      condition ...(string_2 notin builtIn)
      condition unique(string_2) # all symbols must be unique
      condition string_1 notin string_2
      premise ttypes(C_1, texpr_1, typ_1)
      premise ...ttypes(C_1, texpr_2, typ_2)
      condition ...(typ_2 != VoidTy())
      let typ_3 = ProcTy(typ_1, ...typ_2)
      let C_2 = C_1 + C(symbols: {string_1: typ_3})
      let C_3 = C_2 + C(ret: typ_1, symbols: map(zip(string_2, typ_2)))
      premise types(C_3, e_1, typ_4)
      condition typ_4 <:= typ_1
      conclusion C_1, ProcDecl(Ident(string_1), texpr_1, Params(*ParamDecl(Ident(string_2), texpr_2)), e_1), C_2, typ_3

    axiom "S-empty-module", C_1, Module(), C_1, VoidTy()

    rule "S-module-single-proc":
      # a trailing procedure must have no parameters
      where ProcDecl(x, typ, Params(), e), decl_1
      premise toplevel(C_1, decl_1, C_2, ProcTy(typ_1))
      conclusion C_1, Module(decl_1), C_2, typ_1

    rule "S-module-single-type":
      where TypeDecl(x, texpr), decl_1
      premise toplevel(C_1, decl_1, C_2, typ)
      conclusion C_1, Module(decl_1), C_2, VoidTy()

    rule "S-module":
      premise toplevel(C_1, decl_1, C_2, typ)
      premise toplevel(C_2, Module(...decl_2), C_3, typ_1)
      conclusion C_1, Module(decl_1, +decl_2), C_3, typ_1

  # TODO: the static semantics also needs to describe how a `(Module ...)` is
  #      reduced to a `(proc ...)` value, which is what a program is, in the
  #      end: a procedural value

  ## Dynamic Semantics
  ## -----------------
  ##
  ## The semantics describing how expressions reduce to values.

  ## Auxiliary Functions
  ## ~~~~~~~~~~~~~~~~~~~

  func substitute(a: expr, with: string -> e) -> e =
    ## The substitution function, which handles binding values/expressions to
    ## identifiers. Identifiers cannot be shadowed.
    case a
    of Exprs(+e_1):
      Exprs(...(substitute(e_1, with)))
    of Let(ident_1, e_1, e_2):
      Let(ident_1, substitute(e_1, with), substitute(e_2, with))
    of Letrec(ident_1, e_1, e_2):
      Letrec(ident_1, substitute(e_1, with), substitute(e_2, with))
    of If(e_1, e_2, e_3):
      If(substitute(e_1, with), substitute(e_2, with), substitute(e_3, with))
    of Match(e_1, +Rule(As(x_1, texpr_1), e_2)):
      Match(substitute(e_1, with), ...Rule(As(x_1, texpr_1), substitute(e_2, with)))
    of Call(+e_1):
      Call(...substitute(e_1, with))
    of Asgn(e_1, e_2):
      Asgn(substitute(e_1, with), substitute(e_2, with))
    of ArrayCons(+e_1):
      ArrayCons(...substitute(e_1, with))
    of TupleCons(*e_1):
      TupleCons(...substitute(e_1, with))
    of RecordCons(+Field(x_1, e_1)):
      RecordCons(...Field(x_1, substitute(e_1, with)))
    of Seq(texpr_1, *e_1):
      Seq(texpr_1, ...substitute(e_1, with))
    of FieldAccess(e_1, eindex_1):
      FieldAccess(substitute(e_1, with), eindex_1)
    of At(e_1, e_2):
      At(substitute(e_1, with), substitute(e_2, with))
    of As(e_1, texpr_1):
      As(substitute(e_1, with), texpr_1)
    of While(e_1, e_2):
      While(substitute(e_1, with), substitute(e_2, with))
    of Return(e_1):
      Return(substitute(e_1, with))
    of `proc`(typ_1, *[x_2, typ_2], e_1):
      `proc`(typ_1, ...[x_2, typ_2], substitute(e_1, with))
    of Ident(string_1):
      # the actual substitution
      if string_1 in with:
        with(string_1)
      else:
        Ident(string_1)
    of e_1:
      e_1 # nothing to replace

  func intAdd(a, b: n) -> n =
    let n_3 = a + b
    if n_3 < (2 ^ 63):
      if neg(2 ^ 63) <= n_3:
        n_3
      else:
        fail
    else:
      fail

  func intSub(a, b: n) -> n =
    let n_3 = a - b
    if n_3 < (2 ^ 63):
      if neg(2 ^ 63) <= n_3:
        n_3
      else:
        fail
    else:
      fail

  func intMul(a, b: n) -> n =
    let n_3 = a * b
    if n_3 < (2 ^ 63):
      if neg(2 ^ 63) <= n_3:
        n_3
      else:
        fail
    else:
      fail

  func intDiv(a, b: n) -> n =
    case (a, b)
    of n_1, 0: fail
    of n_1, n_2:
      if same(n_1, neg(2 ^ 63)):
        if same(n_2, -1):
          fail
        else:
          trunc(n_1 / n_2)
      else:
        trunc(n_1 / n_2)

  func intMod(a, b: n) -> n =
    case (a, b)
    of n_1, 0: fail
    of n_1, n_2: n_1 - (n_2 * trunc(n_1 / n_2))

  func intCmp(a, b: z) -> equality =
    ## Integer comparison.
    if a < b: Lt
    else:
      if same(a, b): Eq
      else:          Gt

  func opp(s: bool, v: z) -> z =
    case s
    of true:  neg(v)
    of false: v

  func min(a, b: z) -> z =
    if a < b: a else: b
  func max(a, b: z) -> z =
    if a < b: b else: a

  func even(a: n) -> bool = same(a mod 2, 0)

  func `xor`(a, b: bool) -> bool = not same(a, b)

  func digit2(a: n) -> n =
    ## Computes the 1-based position of the most-significant bit.
    case a
    of 0: 0
    of 1: 1
    else:
      # note: only the shift-by-1 branch is needed for correct operation -- the
      # others are only an optimization
      if 2^32 <= a:
        digit2(trunc(a / (2^32))) + 32
      else:
        if 2^16 <= a:
          digit2(trunc(a / (2^16))) + 16
        else:
          if 2^8 <= a:
            digit2(trunc(a / (2^8))) + 8
          else:
            if 2^4 <= a:
              digit2(trunc(a / (2^4))) + 4
            else:
              # shift right by 1
              digit2(trunc(a / 2)) + 1

  # TODO: make the floating-point operators generic over formats by
  #       making the below two defs parameters of the operators
  def emax, 1024
  def prec, 53

  func fexp(exp: z) -> z =
    max(exp - prec, 3 - emax - prec)

  func align(mx: n, ex, ey: z) -> n =
    ## Returns `my` such that `my*(2^ey) = mx*(2^ex)`, when ey < ex.
    if ey < ex:
      mx * (2 ^ (ex - ey))
    else:
      mx

  typ location:
    Exact
    Inexact(equality)

  func toLocation(f: r) -> location =
    if same(f, 0.0):   Exact
    else:
      if same(f, 0.5): Inexact(Eq)
      else:
        if f < 0.5:    Inexact(Lt)
        else:          Inexact(Gt)

  func fnormalize(mx: n, ex: z) -> (n, z, location) =
    ## Right-shifts `mx` such that the most significant bit is at `prec`, if
    ## possible. The resulting exponent stays in the [3-emax-prec, inf) range.
    let shift = fexp(digit2(mx) + ex) - ex
    if 0 < shift:
      let shifted = mx / (2 ^ shift)
      let i = trunc(shifted) # integer part of `shifted`
      (i, ex + shift, toLocation(shifted - i))
    else:
      (mx, ex, Exact)

  func reshift(mx: n, ex: z, lx: location) -> (n, z) =
    ## Adds `lx` as roundings bits to `mx*(2^ex)`.
    case lx
    of Exact:       (mx, ex)
    of Inexact(Lt): (mx * 4 + 1, ex - 2)
    of Inexact(Eq): (mx * 2 + 1, ex - 1)
    of Inexact(Gt): (mx * 4 + 3, ex - 2)

  func roundNearestEven(mx: n, lx: location) -> n =
    ## Implements the floating-point to-nearest, tie-to-even rounding
    ## mode.
    case lx
    of Exact: mx
    of Inexact(Lt): mx # round down
    of Inexact(Eq):
      if even(mx): mx else: (mx + 1) # tie; round to even
    of Inexact(Gt):
      mx + 1 # round up

  func binaryRoundAux(sx: bool, mx: n, ex: z) -> float =
    let (m_1, e_1, lx) = fnormalize(mx, ex) # normalize
    let rnd = roundNearestEven(m_1, lx) # round
    let (m_2, e_2, _) = fnormalize(rnd, e_1) # normalize `rnd`
    case m_2
    of 0: Zero(sx)
    of z_1:
      if z_1 < 0: Nan
      else:
        if e_2 <= (emax - prec): Finite(sx, z_1, e_2)
        else: Inf(sx)

  func binaryRound(s: bool, m: n, exp: z) -> float =
    # if less, left-shift `m` such that its MSB is at `prec` before rounding
    let exp_2 = fexp(digit2(m) + exp)
    let m_2 = align(m, exp, exp_2)
    let exp_3 = min(exp, exp_2)
    binaryRoundAux(s, m_2, exp_3)

  func normalize(m, exp: z, szero: bool) -> float =
    ## Yields the closest possible floating point representation
    ## for `m` and `exp` such that `f ~= m*(2^exp)`.
    case m
    of 0: Zero(szero)
    else:
      if m < 0: binaryRound(true, neg(m), exp)
      else:     binaryRound(false, m, exp)

  func toFloat(s: bool, fac: r, exp: n) -> float =
    ## Turns the rational value `val*(2^exp)` with sign `s` (`fac` must be
    ## positive) into a float value.
    let v = fac * (2^prec) # left-shift the base-2 radix point by `prec`
    let i = trunc(v)
    # turn the fractional part into rounding bits (only two bits of precision
    # are needed)
    let (m, exp_2) = reshift(i, exp - prec, toLocation(v - i))
    # round the result
    binaryRoundAux(s, m, exp_2)

  func floatAdd(a, b: float) -> float =
    ## IEEE-754.2008 binary64 addition (with simplified nans).
    case (a, b)
    of Nan, _: Nan
    of _, Nan: Nan
    of Inf(bool_1), Inf(bool_2):
      if same(bool_1, bool_2): Inf(bool_1)
      else:                    Nan
    of Inf(bool), _: a
    of _, Inf(bool): b
    of Zero(bool_1), Zero(bool_2):
      if same(bool_1, bool_2):
        a
      else:
        Zero(false) # negative + positive = positive
    of Zero(bool), float_1: float_1
    of float_1, Zero(bool): float_1
    of Finite(bool_1, n_1, z_1), Finite(bool_2, n_2, z_2):
      # align the exponents, then add, then normalize the result
      let exp = min(z_1, z_2)
      normalize(
        opp(bool_1, align(n_1, z_1, exp)) + opp(bool_2, align(n_2, z_2, exp)),
        exp, false)

  func floatSub(a, b: float) -> float =
    ## IEEE-754.2008 binary64 subtraction (with simplified nans).
    case (a, b)
    of Nan, _: Nan
    of _, Nan: Nan
    of Inf(bool_1), Inf(bool_2):
      # -inf - inf = -inf
      if same(bool_1, not bool_2): Inf(bool_1)
      else:                        Nan
    of Inf(bool), _: a
    of _, Inf(bool): b
    of Zero(bool_1), Zero(bool_2):
      if same(bool_1, not bool_2):
        a
      else:
        Zero(false)
    of Zero(bool), Finite(bool_1, n_1, z_1):
      # 0 - f inverts the sign of f
      Finite(not bool_1, n_1, z_1)
    of float_1, Zero(bool): float_1
    of Finite(bool_1, n_1, z_1), Finite(bool_2, n_2, z_2):
      # align the exponents, then subtract, then normalize the result
      let exp = min(z_1, z_2)
      normalize(
        opp(bool_1, align(n_1, z_1, exp)) - opp(bool_2, align(n_2, z_2, exp)),
        exp, false)

  func floatMul(a, b: float) -> float =
    ## IEEE-754.2008 binary64 multiplication (with simplified nans).
    case (a, b)
    of Nan, _: Nan
    of _, Nan: Nan
    of Inf(bool), Zero(bool): Nan
    of Zero(bool), Inf(bool): Nan
    of Inf(bool_1), Inf(bool_2):
      Inf(bool_1 xor bool_2)
    of Inf(bool_1), Finite(bool_2, n, z):
      Inf(bool_1 xor bool_2)
    of Finite(bool_2, n, z), Inf(bool_1):
      Inf(bool_1 xor bool_2)
    of Finite(bool_1, n, z), Zero(bool_2):
      Zero(bool_1 xor bool_2)
    of Zero(bool_1), Finite(bool_2, n, z):
      Zero(bool_1 xor bool_2)
    of Zero(bool_1), Zero(bool_2):
      Zero(bool_1 xor bool_2)
    of Finite(bool_1, n_1, z_1), Finite(bool_2, n_2, z_2):
      # x*(2^e_1) * y*(2^e_2) = x*y*(2^(e_1 + e_2))
      # no need to go through `normalize`, because we know that the signficand
      # doesn't need to / cannot be left-shifted
      binaryRoundAux(bool_1 xor bool_2, n_1 * n_2, z_1 + z_2)

  func floatDiv(a, b: float) -> float =
    ## IEEE-754.2008 binary64 division (with simplified nans).
    case (a, b)
    of Nan, _: Nan
    of _, Nan: Nan
    of Inf(bool), Inf(bool):
      Nan
    of Zero(bool), Zero(bool):
      Nan
    of Inf(bool_1), Finite(bool_2, n, z):
      Inf(bool_1 xor bool_2)
    of Finite(bool_1, n, z), Inf(bool_2):
      Zero(bool_1 xor bool_2)
    of Inf(bool_1), Zero(bool_2):
      Inf(bool_1 xor bool_2)
    of Zero(bool_1), Inf(bool_2):
      Zero(bool_1 xor bool_2)
    of Finite(bool_1, n, z), Zero(bool_2):
      Inf(bool_1 xor bool_2)
    of Zero(bool_1), Finite(bool_2, n, z):
      Zero(bool_1 xor bool_2)
    of Finite(bool_1, n_1, z_1), Finite(bool_2, n_2, z_2):
      # x*(2^e_1) / y*(2^e_2) = (x/y) * 2^(e_1-e_2)
      toFloat(bool_1 xor bool_2, n_1 / n_2, z_1 - z_2)

  func floatCmp(a, b: float) -> option =
    ## IEEE-754.2008 binary64 comparison.
    case (a, b)
    of Nan, _: None
    of _, Nan: None
    of Inf(bool_1), Inf(bool_2):
      case (bool_1, bool_2)
      of true, true:   Some(Eq)
      of false, false: Some(Eq)
      of true, false:  Some(Lt)
      of false, true:  Some(Gt)
    of Inf(bool_1), _:
      if bool_1: Some(Lt) else: Some(Gt)
    of _, Inf(bool_1):
      if bool_1: Some(Gt) else: Some(Lt)
    of Finite(bool_1, z, z), Zero(bool):
      if bool_1: Some(Lt) else: Some(Gt)
    of Zero(bool), Finite(bool_1, z, z):
      if bool_1: Some(Lt) else: Some(Gt)
    of Zero(bool), Zero(bool):
      Some(Eq) # sign doesn't matter
    of Finite(bool_1, n_1, z_1), Finite(bool_2, n_2, z_2):
      case (bool_1, bool_2)
      of true, false: Some(Lt)
      of false, true: Some(Gt)
      of false, false:
        case intCmp(z_1, z_2)
        of Lt: Some(Lt)
        of Gt: Some(Gt)
        of Eq: Some(intCmp(n_1, n_2))
      of true, true:
        case intCmp(z_1, z_2)
        of Lt: Some(Gt)
        of Gt: Some(Lt)
        of Eq:
          case intCmp(n_2, n_1)
          of Lt: Some(Gt)
          of Gt: Some(Lt)
          of Eq: Some(Eq)

  func asBool(b: bool) -> val =
    case b
    of true:  True
    of false: False

  func eq(a, b: val) -> val =
    case (a, b)
    of True, True:
      True
    of False, False:
      True
    of False, True:
      False
    of True, False:
      False
    of IntVal(z_1), IntVal(z_2):
      asBool same(intCmp(z_1, z_2), Eq)
    of FloatVal(float_1), FloatVal(float_2):
      asBool same(floatCmp(float_1, float_2), Some(Eq))

  func lt(a, b: val) -> val =
    case (a, b)
    of IntVal(n_1), IntVal(n_2):
      asBool same(intCmp(n_1, n_2), Lt)
    of FloatVal(float_1), FloatVal(float_2):
      asBool same(floatCmp(float_1, float_2), Some(Lt))

  func leq(a, b: val) -> val =
    case (a, b)
    of IntVal(z_1), IntVal(z_2):
      case intCmp(z_1, z_2)
      of Lt: True
      of Eq: True
      of Gt: False
    of FloatVal(float_1), FloatVal(float_2):
      case floatCmp(float_1, float_2)
      of Some(Lt): True
      of Some(Eq): True
      else:        False

  record DC, {locs: (z -> val),
              nloc: z,
              time: z,
              output: val,
              errOutput: val,
              files: ((string, z) -> val)} # name + time -> content
  ## `DC` is the dynamic context

  func utf8Bytes(_: string) -> *z
    # TODO: the function is mostly self-explanatory, but it should be defined in
    #       a bit more detail nonetheless
    ##

  ## Evaluation Contexts
  ## ~~~~~~~~~~~~~~~~~~~

  context L:
    # evaluation context for locs in lvalue expressions
    hole
    FieldAccess(L, eindex)
    At(L, IntVal(n))

  context E:
    hole
    Exprs(E, +e)
    FieldAccess(E, eindex)
    At(E, e)
    At(le, E)
    At(val, E)
    As(E, texpr)
    Asgn(E, e)
    Asgn(le, E)
    With(E, n, e)
    With(val, n, E)
    With(E, string, e)
    With(val, string, E)
    ArrayCons(*val, E, *e)
    TupleCons(*val, E, *e)
    RecordCons(*Field(x, val), Field(x, E), *Field(x, e))
    Seq(typ, *val, E, *e)
    Call(*val, E, *e)
    Call(x, *val, E, *e)
    If(E, e, e)
    Match(E, +rule)
    Let(x, E, e)
    Return(E)

  context F:
    # defines where `loc` values are replaced with their value. These are all
    # positions also described by `E`, minus the LHS of `Asgn` and roots of
    # projections
    Exprs(hole, +e)
    At(le, hole)
    At(val, hole)
    As(hole, texpr)
    Asgn(le, hole)
    With(hole, n, e)
    With(val, n, hole)
    With(hole, string, e)
    With(val, string, hole)
    ArrayCons(*val, hole, *e)
    TupleCons(*val, hole, *e)
    RecordCons(*Field(x, val), Field(x, hole), *Field(x, e))
    Seq(typ, *val, hole, *e)
    Call(*val, hole, *e)
    Call(x, *val, hole, *e)
    If(hole, e, e)
    Match(hole, +rule)
    Let(x, hole, e)
    Return(hole)

  context B:
    hole
    E[B]
    Frame(typ, B)

  ## Reductions and Steps
  ## ~~~~~~~~~~~~~~~~~~~~

  inductive pReducesTo(inp e, out e):
    # pure reductions, that is, reductions not dependent on the execution
    # context
    axiom "E-false", Ident("false"), False
    axiom "E-true",  Ident("true"),  True
    axiom "E-exprs-fold", Exprs(e_1), e_1
    axiom "E-exprs", Exprs(TupleCons(), +e_1), Exprs(...e_1)
    axiom "E-if-true", If(True, e_1, e_2), e_1
    axiom "E-if-false", If(False, e_1, e_2), e_2
    axiom "E-as", As(val_1, texpr), val_1 # a no-op

    axiom "E-while", While(e_1, e_2), If(e_1, Exprs(e_2, While(e_1, e_2)), TupleCons())

    rule "E-match-success":
      premise types(C(ret: VoidTy), val_1, typ_1)
      condition typ_1 == texpr_1
      conclusion Match(val_1, Rule(As(Ident(string_1), texpr_1), e_1), *any),
                 substitute(e_1, {string_1 : val_1})

    rule "E-match-next":
      premise types(C(ret: VoidTy), val_1, typ_1)
      condition typ_1 != texpr_1
      conclusion Match(val_1, Rule(As(x, texpr_1), e), +rule_1),
                 Match(val_1, ...rule_1)

    rule "E-tuple-access":
      where TupleCons(+val_3), val_1
      where val_2, val_3[n_1]
      conclusion FieldAccess(val_1, IntVal(n_1)), val_2

    rule "E-rec-access":
      let val_2 = map(zip(string_1, val_1))(string_2)
      conclusion FieldAccess(RecordCons(+Field(Ident(string_1), val_1)), Ident(string_2)),
                 val_2

    axiom "E-field-asgn", Asgn(FieldAccess(le_1, IntVal(n_1)), val_1), Asgn(le_1, With(le_1, n_1, val_1))
    axiom "E-elem-asgn", Asgn(At(le_1, IntVal(n_1)), val_1), Asgn(le_1, With(le_1, n_1, val_1))
    axiom "E-rec-field-asgn",
          Asgn(FieldAccess(le_1, Ident(string_1)), val_1),
          Asgn(le_1, With(le_1, string_1, val_1))

    axiom "E-seq-cons", Seq(typ, *val_1), `array`(...val_1)

    rule "E-at":
      condition 0 <= n_1
      condition n_1 < len(val_1)
      let val_2 = val_1[n_1]
      conclusion At(array(*val_1), IntVal(n_1)), val_2

    rule "E-at-array":
      condition 0 <= n_1 and n_1 < len(val_1)
      conclusion At(ArrayCons(+val_1), IntVal(n_1)), val_1[n_1]
    rule "E-at-tuple":
      condition 0 <= n_1
      condition n_1 < len(val_1)
      let val_2 = val_1[n_1]
      conclusion At(TupleCons(*val_1), IntVal(n_1)), val_2

    rule "E-at-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion At(array(*val_1), IntVal(n_1)), Unreachable()

    rule "E-at-array-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion At(ArrayCons(+val_1), IntVal(n_1)), Unreachable()
    rule "E-at-tuple-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion At(TupleCons(*val_1), IntVal(n_1)), Unreachable()

    rule "E-with-array":
      # TODO: rename to E-with-seq
      where val_3, array(for y in updated(val_1, n_1, val_2): y)
      conclusion With(array(*val_1), n_1, val_2), val_3
    rule "E-with-array-2":
      where val_3, ArrayCons(for y in updated(val_1, n_1, val_2): y)
      conclusion With(ArrayCons(+val_1), n_1, val_2), val_3
    rule "E-with-tuple":
      where val_3, TupleCons(for y in updated(val_1, n_1, val_2): y)
      conclusion With(TupleCons(+val_1), n_1, val_2), val_3
    rule "E-with-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion With(array(*val_1), n_1, val_2), Unreachable()
    rule "E-with-record":
      let val_3 = updated(val_1, indexOf(string_1, string_2, 0), val_2)
      conclusion With(RecordCons(+Field(Ident(string_1), val_1)), string_2, val_2),
                 RecordCons(...Field(Ident(string_1), val_3))

    rule "E-with-array-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion With(ArrayCons(+val_1), n_1, val_2), Unreachable()
    rule "E-with-tuple-out-of-bounds":
      condition n_1 < 0 or len(val_1) <= n_1
      conclusion With(TupleCons(*val_1), n_1, val_2), Unreachable()

    axiom "E-not-false", Call(Ident("not"), False), True
    axiom "E-not-true",  Call(Ident("not"), True),  False

    rule "E-add-int":
      let n_3 = intAdd(n_1, n_2)
      conclusion Call(Ident("+"), IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-add-int-overflow":
      condition (n_1, n_2) notin intAdd
      conclusion Call(Ident("+"), IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-sub-int":
      let n_3 = intSub(n_1, n_2)
      conclusion Call(Ident("-"), IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-sub-int-overflow":
      condition (n_1, n_2) notin intSub
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
      let n_3 = intMod(n_1, n_2)
      conclusion Call(Ident("mod"), IntVal(n_1), IntVal(n_2)), IntVal(n_3)
    rule "E-mod-int-overflow":
      condition (n_1, n_2) notin intMod
      conclusion Call(Ident("mod"), IntVal(n_1), IntVal(n_2)), Unreachable()

    rule "E-add-float":
      let float_3 = floatAdd(float_1, float_2)
      conclusion Call(Ident("+"), FloatVal(float_1), FloatVal(float_2)), FloatVal(float_3)
    rule "E-sub-float":
      let float_3 = floatSub(float_1, float_2)
      conclusion Call(Ident("-"), FloatVal(float_1), FloatVal(float_2)), FloatVal(float_3)
    rule "E-mul-float":
      let float_3 = floatMul(float_1, float_2)
      conclusion Call(Ident("*"), FloatVal(float_1), FloatVal(float_2)), FloatVal(float_3)
    rule "E-mul-float":
      let float_3 = floatDiv(float_1, float_2)
      conclusion Call(Ident("/"), FloatVal(float_1), FloatVal(float_2)), FloatVal(float_3)

    rule "E-builtin-eq":
      let val_3 = eq(val_1, val_2)
      conclusion Call(Ident("=="), val_1, val_2), val_3
    rule "E-builtin-le":
      let val_3 = leq(val_1, val_2)
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
    rule "E-string-cons":
      # FIXME: doesn't need to be an impure reduction
      where *z_1, utf8Bytes(string_1)
      conclusion DC_1, Seq(StringVal(string_1)), DC_1, array(...IntVal(z_1))

    rule "E-let-introduce":
      let z_1 = DC_1.nloc
      let DC_2 = DC_1 + DC(locs: {z_1 : val_1}, nloc: z_1 + 1)
      let e_2 = substitute(e_1, {string_1: loc(z_1)})
      conclusion DC_1, Let(Ident(string_1), val_1, e_1), DC_2, e_2
    # TODO: the location needs to be removed from the execution context once
    #       `e_2` is reduced to a value, otherwise it remains accessible. This
    #       is not a problem at the moment, but it will be once there are
    #       first-class locations (e.g., pointers) in the source language.
    #       Removing the location from the store could be achieved via a new
    #       `(Pop x)` construct, where `(Let x val e)` reduces to `(Pop x e)`

    rule "E-letrec":
      let z_1 = DC_1.nloc
      where val_2, substitute(val_1, {string_1: loc(z_1)})
      let DC_2 = DC_1 + DC(locs: {z_1 : val_2}, nloc: z_1 + 1)
      let e_2 = substitute(e_1, {string_1: loc(z_1)})
      conclusion DC_1, Letrec(Ident(string_1), val_1, e_1), DC_2, e_2

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
      conclusion DC_1, B_1[e_1], DC_1, B_1[e_2]

    rule "E-reduce-impure":
      premise reducesTo(DC_1, e_1, DC_2, e_2)
      conclusion DC_1, B_1[e_1], DC_2, B_1[e_2]

    rule "E-load":
      # an automatic load only takes place:
      # * outside of lvalue positions
      # * in the root of otherwise fully evaluated lvalue expressions
      conclusion DC_1, B_1[F_1[L_1[loc(z_1)]]],
                 DC_1, B_1[F_1[L_1[DC_1.locs(z_1)]]]
    rule "E-load-top":
      # top-level version of E-load
      conclusion DC_1, L_1[loc(z_1)],
                 DC_1, L_1[DC_1.locs(z_1)]

    rule "E-return":
      conclusion DC_1, B_1[Frame(typ_1, E_1[Return(val_1)])],
                 DC_1, B_1[Frame(typ_1, val_1)]
    rule "E-return-unit":
      conclusion DC_1, B_1[Frame(typ_1, E_1[Return()])],
                 DC_1, B_1[Frame(typ_1, TupleCons())]
    rule "E-unwind":
      conclusion DC_1, B_1[Frame(typ, val_1)],
                 DC_1, B_1[val_1]

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

  func reduceModule(a: module) -> expr =
    ## Describes how a module is reduced to an expression.
    case a
    of Module(ProcDecl(x_1, typ_1, Params(), e_1)):
      # the trailing procedure declaration is the main procedure; it's called
      # implicitly
      Letrec(x_1, `proc`(typ_1, e_1), Call(x_1))
    of Module(ProcDecl(x_1, typ_1, Params(*ParamDecl(x_2, typ_2)), e_1), *TypeDecl(x, texpr), +decl_1):
      Letrec(x_1, `proc`(typ_1, ...[x_2, typ_2], e_1), reduceModule(Module(...decl_1)))
    of Module(*TypeDecl(x, texpr)):
      Unreachable()
    of Module(+TypeDecl(x, texpr), +decl_1):
      reduceModule(Module(...decl_1))

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

  func `not`(b: bool) -> bool =
    case b
    of true: false
    of false: true

  # XXX: the built-in `in` function should consider the custom equality
  #      operator, which would render `contains` obsolete
  func contains(list: *typ, t: typ) -> bool =
    case list
    of [typ_1, *typ_2]:
      if typ_1 == t:
        true
      else:
        contains(typ_2, t)
    of _:
      false

  func identical(set_1, set_2: *typ) -> bool =
    ## Treats the lists as sets and computes whether they're equal.
    if (for a in set_1: contains(set_2, a)):
      if (for a in set_2: contains(set_1, a)):
        true
      else:
        false
    else:
      false

  func mapContains(list: *(string, typ), p: (string, typ)) -> bool =
    let (s, t) = p
    let m = map(list)
    s in m and m(s) == t

  func uniqueTypes(list: *typ) -> bool =
    ## Computes whether all types in the list are unique.
    case list
    of [typ_1, +typ_2]:
      if not contains(typ_2, typ_1):
        uniqueTypes(typ_2)
      else:
        false
    of _:
      true

  func unique(list: *string) -> bool =
    ## Computes whether all strings in the list are unique.
    case list
    of [string_1, +string_2]:
      if string_1 notin string_2:
        unique(string_2)
      else:
        false
    of _:
      true

  func indexOf(list: *string, it: string, i: n) -> n =
    case list
    of [string_1, *string_2]:
      if same(string_1, it):
        i
      else:
        indexOf(string_2, it, i + 1)
