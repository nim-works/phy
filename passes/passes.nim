## The home of all intermediate languages and passes, representing the core of
## the compiler.

import
  nanopass/nanopass,
  experimental/sexp_parse

defineLanguage Lsrc:
  n(int)
  fl(float)
  str(string)
  # TODO: only allow a type being used as a terminal once
  x(string) # identifier

  rec_field(rf) ::= Field(x, e)
  field_decl(f) ::= Field(x, t)

  pattern(p) ::= As(x, t)
  mrule(mr) ::= Rule(p, e)
  expr(e) ::= n | fl | x |
              ArrayCons(...e) |
              TupleCons(...e) |
              RecordCons(rf0, ...rf1) |
              Seq(t, ...e) |
              Seq(str) |
              Call(e, ...e) |
              FieldAccess(e, n) |
              FieldAccess(e, x) |
              At(e0, e1) |
              As(e, t) |
              And(e0, e1) |
              Or(e0, e1) |
              If(e0, e1) |
              If(e0, e1, e2) |
              While(e0, e1) |
              Return(e) |
              Unreachable() |
              Exprs(...e0, e1) |
              Asgn(e0, e1) |
              Decl(x, e) |
              Match(e, mr0, ...mr1)
  typ(t) ::= x | VoidTy() | UnitTy() | BoolTy() | IntTy() | FloatTy() |
             ArrayTy(n, t) |
             SeqTy(t) |
             TupleTy(t0, ...t1) |
             RecordTy(f0, ...f1) |
             UnionTy(t0, ...t1) |
             ProcTy(t0, ...t1)

  param_decl(pd) ::= ParamDecl(x, t)
  params(pa)     ::= Params(...pd)
  decl(d)        ::= ProcDecl(x, t, pa, e) | TypeDecl(x, t)
  module(m)      ::= Module(...d)

defineLanguage L1, Lsrc:
  ## Language without And and Or.
  expr(e) ::= -And(e, e) | -Or(e, e)

defineLanguage L2, L1:
  ## Language without single-branch `If`.
  expr(e) ::= -If(e, e)

defineLanguage L3, L2:
  ## Language that replaces Decl with Let.
  expr(e) ::= -Decl(x, e) | +Let(x, e, e)

defineLanguage L4, L3:
  ## Removes the `Match` form.
  pattern(p) ::= -As(x, t)
  mrule(mr) ::= -Rule(p, e)
  expr(e) ::= -Match(e, mr, ...mr)

defineLanguage L5, L4:
  ## Removes the While form and adds the Loop and Break form.
  expr(e) ::= -While(e, e) | +Loop(e) | +Break(n)

defineLanguage L6, L5:
  ## Requires explicit copies.
  root(ro) ::= +lv | +e
  lvalue(lv) ::=
    +At(ro, e) |
    +FieldAccess(ro, n)
  expr(e) ::=
    -At(e, e) |
    -FieldAccess(e, n) |
    +Copy(lv)

proc parse(s: var SexpParser): Lsrc {.inpass.} =
  ## Parses the source language from an S-expression stream.
  proc ident(s: var SexpParser): dst.x {.transform.} =
    s.space()
    s.expect(tkIdent)
    build x(s.eatString())

  proc call(s: var SexpParser): dst.e {.transform.} =
    let callee = expr(s)
    var x = @[expr(s)]
    s.space()
    while s.currToken != tkParensRi:
      expr(s)
      s.space()

    s.eat(tkParensRi)
    build Call(callee, x)

  proc expr(s: var SexpParser): dst.e {.transform.} =
    s.space()
    case s.currToken
    of tkParsensLe:
      let k = s.getTok()
      if k == tkIdent:
        case s.currString
        of "if":
          build If(expr(s), expr(s), expr(s))
        of "while":
          build While(expr(s), expr(s))
        of "decl":
          build Decl(ident(s), expr(s))
        of "and":
          build And(expr(s), expr(s))
        of "or":
          build Or(expr(s), expr(s))
        else:
          # TODO: implement the remaining keywords
          call(s)
      else:
        call(s)

    of tkString:
      build str(s.eatString())
    of tkIdent:
      build x(s.eatString())
    of tkInt:
      build n(parseInt(s.eatString()))
    of tkFloat:
      build fl(parseFloat(s.eatString()))
    else:
      syntaxError(s)

  proc typ(s: var SexpParser): dst.t {.transform.} =
    s.space()
    # TODO: implement

  proc params(s: var SexprParser): dst.pa {.transform.} =
    s.space()
    # TODO: implement

  proc top(s: var SexpParser): dst.d {.transform.} =
    s.eat(tkParensLe)
    s.expect(tkIdent)
    case s.currToken
    of "proc":
      build ProcDecl(ident(s), typ(s), params(s), expr(s))
    of "type":
      build TypeDecl(ident(s), typ(s))
    else:
      syntaxError()

proc removeAndOr(_: Lsrc): L1 {.pass.} =
  proc expr(_: src.e): dst.e {.transform.} =
    And([a], [b]) -> build If(a, b, x("false"))
    Or([a], [b]) -> build If(a, x("true"), b)

proc removeSingleIf(_: L1): L2 {.pass.} =
  proc expr(_: src.e): dst.e {.transform.} =
    If([a], [b]) -> build If(a, b, TupleCons())

proc declToLet(_: L2): L3 {.pass.} =
  proc expr(_: src.e): dst.e {.transform.} =
    Decl(`x`, `e`) -> build Let(x, e, TupleCons())
    Exprs(`e0`, [last]):
      var r = last
      var got: seq[dst.e]
      for i in countdown(e0.high, 0):
        match e0[i]:
          Decl(`x`, `e`):
            r =
              if got.len == 0: build Let(x, e, r)
              else:            build Let(x, e, Exprs(got, r))
          else:
            got.insert expr(e0[i])

      if got.len == 0: build Exprs(got, r)
      else:            r
