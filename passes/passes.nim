## The home of all intermediate languages and passes, representing the core of
## the compiler.

import
  std/[
    streams,
    strformat,
    strutils,
    tables
  ],
  nanopass/nanopass,
  experimental/sexp_parse,
  passes/trees,
  phy/[reporting, default_reporting]

type
  Symbol = object
  Ident = distinct string

defineLanguage Lsrc:
  n(int)
  fl(float)
  str(string)
  x(Ident)

  rec_field(rf) ::= Field(x, e)
  field_decl(f) ::= Field(x, t)

  pattern(p) ::= As(x, t)
  mrule(mr) ::= Rule(p, e)
  expr(e) ::= n | fl | x | str |
              ArrayCons(...e) |
              TupleCons(...e) |
              RecordCons(rf, ...rf) |
              Seq(t, ...e) |
              Seq(str) |
              Call(e, ...e) |
              FieldAccess(e, n) |
              FieldAccess(e, x) |
              At(e, e) |
              As(e, t) |
              And(e, e) |
              Or(e, e) |
              If(e, e) |
              If(e, e, e) |
              While(e, e) |
              Return(e) |
              Unreachable() |
              Exprs(...e, e) |
              Asgn(e, e) |
              Decl(x, e) |
              Match(e, mr, ...mr)
  typ(t) ::= x | VoidTy() | UnitTy() | BoolTy() | CharTy() | IntTy() | FloatTy() |
             ArrayTy(n, t) |
             SeqTy(t) |
             TupleTy(t, ...t) |
             RecordTy(f, ...f) |
             UnionTy(t, ...t) |
             ProcTy(t, ...t)

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
  ## Language with symbols instead of raw identifiers.
  +s(Symbol)
  expr(e) ::= -x | +s |
              -Let(x, e, e) | +Let(s, e, e)
  typ(t)  ::= -x | +s
  pattern(p) ::= -As(x, t) | +As(t, s) # the element order is swapped

  param_decl(pd) ::= -ParamDecl(x, t) | +ParamDecl(s, t)
  decl(d)        ::= -ProcDecl(x, t, pa, e) | +ProcDecl(s, t, pa, e) |
                     -TypeDecl(x, t) | +TypeDecl(s, t)

defineLanguage L5, L4:
  ## Language with type information.
  # expressions that always have the same type don't use a type tag
  expr(e) ::= -ArrayCons(...e) | +ArrayCons(t, ...e) |
              -TupleCons(...e) | +TupleCons(t, e, ...e) |
              -RecordCons(rf, ...rf) | +RecordCons(t, rf, ...rf) |
              -Seq(str) | +Seq(t, str) |
              -Call(e, ...e) | +Call(t, e, ...e) |
              -FieldAccess(e, n) | +FieldAccess(t, e, n) |
              -FieldAccess(e, x) | +FieldAccess(t, e, x) |
              -At(e, e) | +At(t, e, e) |
              -As(e, t) | +As(t, e, t) |
              -If(e, e, e) | +If(t, e, e, e) |
              -Exprs(...e, e) | +Exprs(t, ...e, e) |
              -Match(e, mr, ...mr) | +Match(t, e, mr, ...mr) |
              +Unit() |
              +Prim(t, str, ...e) # primitive calls (i.e., magic operations)

defineLanguage Lnoas, L5:
  ## Language with more specific forms instead of the generic `As`.
  expr(e) ::= -As(t, e, t) | +Inj(t, e, t)

defineLanguage L6, Lnoas:
  ## Language with the `Match` from removed.
  pattern(p) ::= -As(t, s)
  mrule(mr) ::= -Rule(p, e)
  expr(e) ::= -Match(t, e, mr, ...mr) |
              +Is(t, e, t) |
              +Unpack(t, e)

defineLanguage L7, L6:
  ## Language with no tagged unions, only untagged unions.
  expr(e) ::= -Is(t, e, t) | -Unpack(t, e)

defineLanguage L8, L7:
  ## Language without records.
  rec_field(rf) ::= -Field(x, e)
  field_decl(f) ::= -Field(x, t)
  expr(e) ::= -RecordCons(t, rf, ...rf) | -FieldAccess(t, e, x)
  typ(t) ::= -RecordTy(f, ...f)

defineLanguage L9, L8:
  ## Language where copies are explicit and all aggregate access has a named
  ## local as the root.
  lvalue(lv) ::=
    +s |
    +At(t, lv, e) |
    +FieldAccess(t, lv, n)
  expr(e) ::=
    -s |
    -At(t, e, e) |
    -FieldAccess(t, e, n) |
    +lv |
    +Copy(t, lv)

defineLanguage Lseq, L9:
  ## Language with no built-in sequence values nor types.
  # a "box" is a single-owner single value container
  expr(e) ::= -Seq(t, ...e) | -Seq(t, str) | +Box(t, e) | +Unbox(t, e)
  typ(t) ::= -SeqTy(t) | +BoxTy(t)

defineLanguage Lnocopy, Lseq:
  ## Language without `Copy` form.
  expr(e) ::= -Copy(t, lv)

defineLanguage Lnobox, Lnocopy:
  expr(e) ::= -Box(t, e) | -Unbox(t, e)
  typ(t) ::= -BoxTy(t) | +PtrTy()

defineLanguage Lnocons, Lnobox:
  ## Language without aggregate constructors.
  init(ie) ::= +e | +Undef()
  expr(e) ::= -Let(s, e, e) | +Let(s, ie, e) |
              -ArrayCons(t, ...e) |
              -TupleCons(t, e, ...e,)

defineLanguage Lnoletwithval, Lnocons:
  ## Language without Let initializers.
  init(ie) ::= -e | -Undef()
  expr(e) ::= -Let(s, ie, e) | +Let(s, e)

defineLanguage Lstmt, Lnoletwithval:
  ## Language with a statement/expression separation.
  expr(e) ::= -Asgn(e, e) |
              -Unreachable() |
              -Return(e) |
              -While(e, e) |
              -Exprs(t, ...e, e) |
              +Exprs(t, ...st, e)
  stmt(st) ::= +Asgn(e, e) |
               +Unreachable() |
               +Return(e) |
               +While(e, st) |
               +Pass() | # statement without effect
               +Call(t, e, ...e) |
               +If(e, st, st) | +If(e, st) |
               +Let(s, st) |
               +Stmts(...st, st)
  decl(d) ::= -ProcDecl(s, t, pa, e) | +ProcDecl(s, t, pa, st)

defineLanguage L10, Lstmt:
  ## Language with no If expressions.
  expr(e) ::= -If(t, e, e, e)

defineLanguage L11, L10:
  ## Language with only blob and scalar types.
  lvalue(lv) ::= -s |
                 -FieldAccess(t, lv, n) |
                 -At(t, lv, e)
  expr(e)    ::= -lv |
                 +s |
                 +Offset(t, e, e, n) |
                 +Load(t, e) |
                 +Addr(s)
  stmt(st)   ::= -Asgn(e, e) |
                 +Asgn(s, e) |
                 +Store(e, e)

defineLanguage L12, L11:
  ## Language with only simple callee expressions.
  expr(e)  ::= -Call(t, e, ...e) | +Call(t, s, ...e)
  stmt(st) ::= -Call(t, e, ...e) | +Call(t, s, ...e)

proc eatString(s: var SexpParser): string =
  result = s.captureCurrString()
  discard s.getTok()

proc expect(s: SexpParser, kind: TTokKind) =
  if s.currToken != kind:
    # TODO: report a proper syntax error
    raise ValueError.newException("expected " & $kind & ", got " & $s.currToken)

proc eat(s: var SexpParser, kind: TTokKind) =
  s.expect(kind)
  discard s.getTok()

proc parse(s: var SexpParser): Lsrc {.inpass.} =
  ## Parses the source language from an S-expression stream.
  # note: the implementation is incomplete and incorrect (there's also no
  # formal grammar backing it)
  proc expr(s: var SexpParser): dst.e {.transform.}
  proc typ(s: var SexpParser): dst.t {.transform.}

  proc ident(s: var SexpParser): dst.x {.transform.} =
    s.space()
    s.expect(tkSymbol)
    terminal Ident(s.eatString())

  proc call(s: var SexpParser): dst.e {.transform.} =
    # note: does not handle the parenthesis
    let callee = expr(s)
    var args = newSeq[dst.e]()
    s.space()
    while s.currToken != tkParensRi:
      args.add expr(s)
      s.space()

    build Call(callee, args)

  proc pattern(s: var SexpParser): dst.p {.transform.} =
    s.eat(tkParensLe)
    s.expect(tkSymbol)
    let name = s.eatString()
    s.space()
    let t = typ(s)
    s.eat(tkParensRi)
    build As(x(^Ident(name)), t)

  proc rule(s: var SexpParser): dst.mr {.transform.} =
    s.eat(tkParensLe)
    s.eat(tkSymbol)
    # TODO: make sure the symbol is "rule"
    s.space()
    let p = pattern(s)
    s.space()
    let body = expr(s)
    s.eat(tkParensRi)
    build Rule(p, body)

  proc expr(s: var SexpParser): dst.e {.transform.} =
    s.space()
    case s.currToken
    of tkParensLe:
      let k = s.getTok()
      if k == tkSymbol:
        case s.currString
        of "if":
          discard s.getTok()
          result = build If(^expr(s), ^expr(s), ^expr(s))
        of "while":
          discard s.getTok()
          result = build While(^expr(s), ^expr(s))
        of "decl":
          discard s.getTok()
          result = build Decl(^ident(s), ^expr(s))
        of "and":
          discard s.getTok()
          result = build And(^expr(s), ^expr(s))
        of "or":
          discard s.getTok()
          result = build Or(^expr(s), ^expr(s))
        of "as":
          discard s.getTok()
          result = build As(^expr(s), ^typ(s))
        of "exprs":
          discard s.getTok()
          s.space()
          var elems: seq[dst.e]
          while s.currToken != tkParensRi:
            elems.add expr(s)
            s.space()

          let last = elems.pop()
          result = build Exprs(elems, last)
        of "match":
          discard s.getTok()
          let e = expr(s)
          s.space()
          let first = rule(s)
          s.space()
          var next: seq[dst.mr]
          while s.currToken != tkParensRi:
            next.add rule(s)
            s.space()
          result = build Match(e, first, next)
        else:
          # TODO: implement the remaining keywords
          result = call(s)
      else:
        result = call(s)

      s.eat(tkParensRi)
    of tkString:
      result = build(dst.e, str(^s.eatString()))
    of tkSymbol:
      result = build x(^Ident(s.eatString()))
    of tkInt:
      result = build n(^parseInt(s.eatString()))
    of tkFloat:
      result = build fl(^parseFloat(s.eatString()))
    else:
      raise ValueError.newException($s.currToken)
      # syntaxError(s, "expected expression, but got " & )

  proc typ(s: var SexpParser): dst.t {.transform.} =
    s.space()
    s.eat(tkParensLe)
    s.expect(tkSymbol)
    let str = s.eatString()
    case str
    of "bool":  result = build BoolTy()
    of "int":   result = build IntTy()
    of "float": result = build FloatTy()
    of "union":
      let first = typ(s)
      s.space()
      var e: seq[dst.t]
      while s.currToken != tkParensRi:
        e.add typ(s)
        s.space()
      result = build UnionTy(first, e)
    else:
      result = build x(str)
    s.eat(tkParensRi)

  proc param(s: var SexpParser): dst.pd {.transform.} =
    s.eat(tkParensLe)
    result = build ParamDecl(^ident(s), ^typ(s))
    s.space()
    s.eat(tkParensRi)

  proc params(s: var SexpParser): dst.pa {.transform.} =
    var p: seq[dst.pd]
    s.space()
    s.eat(tkParensLe)
    while s.currToken != tkParensRi:
      p.add param(s)
      s.space()
    s.eat(tkParensRi)
    build Params(p)

  proc top(s: var SexpParser): dst.d {.transform.} =
    s.eat(tkParensLe)
    s.expect(tkSymbol)
    case s.eatString()
    of "proc":
      result = build ProcDecl(^ident(s), ^typ(s), ^params(s), ^expr(s))
    of "type":
      result = build TypeDecl(^ident(s), ^typ(s))
    else:
      # TODO: proper syntax error
      raise ValueError.newException("")
    s.eat(tkParensRi)

  proc module(s: var SexpParser): dst.m {.transform.} =
    s.space()
    var decls: seq[dst.d]
    while s.currToken != tkEof:
      decls.add top(s)
      s.space()
    build Module(decls)

  module(s)

proc removeAndOr(x: Lsrc): L1 {.pass.} =
  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of And([e0], [e1]): build If(e0, e1, x(^Ident("false")))
    of Or([e0], [e1]):  build If(e0, x(^Ident("true")), e1)

proc removeSingleIf(x: L1): L2 {.pass.} =
  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of If([e0], [e1]): build If(e0, e1, TupleCons([]))

proc declToLet(x: L2): L3 {.pass.} =
  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of Decl(x, [e]):
      build Let(x, e, TupleCons([]))
    of Exprs(e0, [e1]):
      var r = e1
      var got: seq[dst.e]
      for i in countdown(e0.high, 0):
        match e0[i]:
        of Decl(x, e):
          r =
            if got.len == 0: build Let(x, ^expr(e), r)
            else:            build Let(x, ^expr(e), Exprs(got, r))
        else:
          got.insert expr(e0[i])

      if got.len == 0: build Exprs(got, r)
      else:            r

proc symbolize(x: L3, r: ref ReportContext[string]): L4 {.pass.} =
  ## Binds all identifiers to symbols.
  var ctx: Table[string, Value[Symbol]]
  proc error(msg: string) =
    r.error(msg)

  proc add(name: sink string): Value[Symbol] =
    if name in ctx:
      error(fmt"'{name}' has a symbol bound already")
    result = terminal Symbol()
    ctx[name] = result

  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of Let(x, e0, e1):
      let a = expr(e0)
      let s = add(x.val.string)
      let b = expr(e1)
      # the symbol goes out of scope at the end of the Let
      ctx.del(x.val.string)
      build Let(s, a, b)
    of x:
      if x.val.string in ctx:
        build ^ctx[x.val.string]
      else:
        error(fmt"undeclared identifier: '{x.val.string}'")
        build s(^Symbol()) # error correction

  proc typ(n: src.t): dst.t {.transform.} =
    case n
    of x:
      if x.val.string in ctx:
        build ^ctx[x.val.string]
      else:
        error(fmt"undeclared identifier: '{x.val.string}'")
        build s(^Symbol()) # error correction

  proc rule(n: src.mr): dst.mr {.transform.} =
    case n
    of Rule(p, e):
      match p:
      of As(x, t):
        let s = add(x.val.string)
        let e2 = expr(e)
        ctx.del(x.val.string)
        build Rule(As(^typ(t), s), e2)

  proc param(n: src.pd): dst.pd {.transform.} =
    case n
    of ParamDecl(x, [t]):
      build ParamDecl(^add(x.val.string), t)

  proc params(n: src.pa): dst.pa {.generated.}

  proc decl(n: src.d): dst.d {.transform.} =
    case n
    of ProcDecl(x, t, pa, e):
      let s = add(x.val.string)
      build ProcDecl(s, ^typ(t), ^params(pa), ^expr(e))
    of TypeDecl(x, [t]):
      build TypeDecl(^add(x.val.string), t)

proc typeCheck(x: L4): L5 {.pass.} =
  proc expr(n: src.e): dst.e {.transform.} =
    # XXX: temporary implementation, just so that something exists
    case n
    of ArrayCons([e]):
      build ArrayCons(UnitTy(), e)
    of TupleCons([e]):
      if e.len == 0: build Unit()
      else:          build TupleCons(UnitTy(), ^e[0], e) # FIXME
    of RecordCons([rf0], [rf1]):
      build RecordCons(UnitTy(), rf0, rf1)
    of Seq(str):
      build Seq(SeqTy(CharTy()), str)
    of Seq([t], [e]):
      build Seq(SeqTy(t), e)
    of Call([e0], [e1]):
      build Call(UnitTy(), e0, e1)
    of FieldAccess([e], n):
      build FieldAccess(UnitTy(), e, n)
    of FieldAccess([e], x):
      build FieldAccess(UnitTy(), e, x)
    of At([e0], [e1]):
      build At(UnitTy(), e0, e1)
    of If([e0], [e1], [e2]):
      build If(UnitTy(), e0, e1, e2)
    of As([e], [t]):
      build As(t, e, t)
    of Exprs([e0], [e1]):
      build Exprs(UnitTy(), e0, e1)
    of Match([e], [mr0], [mr1]):
      build Match(UnitTy(), e, mr0, mr1)

proc specializeAs(x: L5): Lnoas {.pass.} =
  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of As([t0], [e], [t1]):
      # TODO: handle the non-union-constructor meaning of `As` (i.e., turn
      #       into an `Exprs`)
      build Inj(t0, e, t1)

proc lowerMatch(x: Lnoas): L6 {.pass.} =
  ## Replaces `Match` forms with chains of if expressions.
  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of Match([t], [e], mr0, mr1):
      proc wrap(tmp: dst.s, r: src.mr, last: dst.e): dst.e =
        match r:
        of Rule(p, e):
          match p:
          of As([t2], s):
            build If(t, Is(BoolTy(), tmp, t2),
              Let(s, Unpack(t2, tmp), ^expr(e)), last)

      let tmp = terminal Symbol()
      var last = build Unit()
      # TODO: ^^ use `Unreachable`. Presently doesn't work due to a pass
      #       ordering issue
      for i in countdown(mr1.high, 0):
        last = wrap(tmp, mr1[i], last)
      build Let(tmp, e, ^wrap(tmp, mr0, last))


proc nounion(x: L6): L7 {.pass.} =
  # TODO: use a proper name
  proc same(a, b: src.t): bool =
    # TODO: implement this somehow. Structural tree equality should likely
    #       just be provided by the framework
    false

  proc computeTag(union, elem: src.t): int =
    match union:
    of UnionTy(t0, t1):
      if same(t0, elem):
        0
      else:
        var r = 0
        # for i, it in t1.pairs:
        #   if same(it.index, elem.index):
        #     r = i
        #     break
        r
    else:
      unreachable()

  proc getType(n: src.e): src.t =
    # TODO: figure out some way to use '_' for elements (to discard them)
    match n:
    of Call(t, e0, e1): t
    of If(t, e0, e1, e2): t
    # TODO: complete
    else: unreachable()

  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of Is([t], e, t1):
      # replace with a tag comparison
      let u = getType(e)
      build Prim(t, str(^"eq"),
        [FieldAccess(IntTy(), ^expr(e), n(^0)), n(^computeTag(u, t1))])
    of Unpack([t], [e]):
      # XXX: how to best get access to the lowered type?
      build FieldAccess(t, FieldAccess(t, e, n(^1)), n(^0))
    of Inj(t0, [e], t1):
      build TupleCons(^typ(t0), n(^computeTag(t0, t1)), [e])

  proc typ(n: src.t): dst.t {.transform.} =
    case n
    of UnionTy([t0], [t1]):
      # becomes a tag + union
      build TupleTy(IntTy(), [UnionTy(t0, t1)])

proc norecord(x: L7): L8 {.pass.} =
  # TODO: use a proper name
  proc fdef(n: src.rf): dst.e {.transform.} =
    case n
    of Field(x, [e]): e

  proc fdef(n: src.f): dst.t {.transform.} =
    case n
    of Field(x, [t]): t

  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of RecordCons([t], [e0], [e1]):
      # TODO: sort the fields while ensuring correct evaluation order
      build TupleCons(t, e0, e1)
    of FieldAccess([t], [e], x):
      build FieldAccess(t, e, n(^0)) # TODO: use the correct index

  proc typ(n: src.t): dst.t {.transform.} =
    case n
    of RecordTy([t0], [t1]):
      # TODO: sort the fields, so that `RecordTy(IntTy(), FloatTy())` and
      #       `RecordTy(FloatTy(), IntTy())` both produce the same
      build TupleTy(t0, t1)

proc bridge(x: L8): Lnocons {.pass.} =
  ## Pass to bridge between some ILs for which the intermediate lowering
  ## passes are still missing.
  # TODO: implement the intermediate passes
  proc typ(n: src.t): dst.t {.transform.} =
    case n
    of SeqTy(t): build BoolTy()

  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of Seq(t, e): build Unit()
    of Seq(t, str): build Unit()
    of Let(s, [e1], [e2]): build Let(s, e1, e2)
    of ArrayCons(t, e): build Unit()
    of TupleCons(t, e0, e1): build Unit()
    of FieldAccess(t, e, n): build Unit()
    of At(t, e0, e1): build Unit()

proc simplifyLet(x: Lnocons): Lnoletwithval {.pass.} =
  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of Let(s, ie, [e]):
      match ie:
      of Undef(): build Let(s, e)
      of e1:      build Let(s, Exprs(UnitTy(), [Asgn(s, ^expr(e1))], e))

proc exprToStmt(x: Lnoletwithval): Lstmt {.pass.} =
  proc etos(n: src.e): dst.st {.transform.} =
    case n
    # TODO: auto-generate transforms such as, e.g., `Let(s, [st]) -> Let(s, st)`
    of Let(s, [st]): build Let(s, st)
    of Unit(): build Pass() # a trailing Unit expression becomes Pass
    of If(t, [e], [st], e2):
      match e2:
      of Unit(): build If(e, st)
      else:      build If(e, st, ^etos(e2))
    of Exprs(t, [st0], [st1]):
      build Stmts(st0, st1)
    of While([e], [st]):
      build While(e, st)
    # TODO: also auto-generate the below
    of Asgn([e0], [e1]): build Asgn(e0, e1)
    of Return([e]):      build Return(e)
    of Unreachable():    build Unreachable()
    else:
      # TODO: maybe raise a proper run-time error? It would allow for better
      #       error messages and thus easier development
      unreachable()

  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of Exprs([t], [st], [e]): build Exprs(t, st, e)
    of Asgn([e0], [e1]):
      build Exprs(UnitTy(), [Asgn(e0, e1)], Unit())
    of While([e], [st]):
      build Exprs(UnitTy(), [While(e, st)], Unit())
    # TODO: auto-generate the exception raising? Right now, a static error is
    #       reported, but - for convenience - the nanopass framework could
    #       also just leave reporting an error to the runtime (Scheme's
    #       nanopass framework does it that way, for what it's worth)
    of Return(e):
      raise ValueError.newException("not an expr")
    of Unreachable():
      raise ValueError.newException("not an expr")

  proc decl(n: src.d): dst.d {.transform.} =
    # TODO: move this to a separate pass and handle void bodies correctly
    case n
    of ProcDecl(s, [t], [pa], [e]): build ProcDecl(s, t, pa, Return(e))

proc ifExprToStmt(x: Lstmt): L10 {.pass.} =
  # TODO: needs to happen earlier
  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of If([t], [e0], [e1], [e2]):
      let s = terminal Symbol()
      build Let(s, Exprs(t, [If(e0, Asgn(s, e1), Asgn(s, e2))], s))

proc blobify(x: L10): L11 {.pass.} =
  ## Turns all aggregate types into blob types.
  proc lval(n: src.lv): (dst.t, dst.e) =
    match n:
    of s:
      # TODO: use the correct expression type
      (build(dst.t, UnitTy()), build(dst.e, Addr(s)))
    of At([t], lv, e):
      let (elem, x) = lval(lv)
      # TODO: use the correct stride (taken from the `elem`)
      (t, build(dst.e, Offset(PtrTy(), x, ^expr(e), n(^1))))
    of FieldAccess([t], lv, n):
      let (elem, x) = lval(lv)
      # TODO: use the correct offset
      (t, build(dst.e, Offset(PtrTy(), x, n, n(^1))))

  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of lv:
      let (t, e) = lval(lv)
      build Load(t, e)

  proc stmt(n: src.st): dst.st {.transform.} =
    case n
    of Asgn(e0, [e1]):
      match e0:
      of lv: build Store(^(lval(lv)[1]), e1)
      else:  unreachable()

proc calleeToSymbol(x: L11): L12 {.pass.} =
  ## Removes all complex callee expressions.
  proc expr(n: src.e): dst.e {.transform.} =
    case n
    of Call([t], e0, [e1]):
      match e0:
      of s: build Call(t, s, e1)
      else:
        let tmp = terminal Symbol()
        build Let(tmp, Exprs(t, [Asgn(tmp, ^expr(e0))], Call(t, tmp, e1)))

  proc stmt(n: src.st): dst.st {.transform.} =
    case n
    of Call([t], e0, [e1]):
      match e0:
      of s: build Call(t, s, e1)
      else:
        let tmp = terminal Symbol()
        build Let(tmp, Stmts([Asgn(tmp, ^expr(e0))], Call(t, tmp, e1)))


# TODO: fix the symbol binding in the pass DSL such that `vmenv` can be
#       imported at the top (at the moment, ambiguity errors ensue)
import vm/[vmmodules, vmspec, vmenv]

type TypeKind = enum
  tkInt, tkFloat, tkPtr, tkBlob

# XXX: doesn't work yet
#[
proc genvm(x: L12): VmModule {.outpass.} =
  ## VM code generator. Generates a VM module from `x`.
  type Assembler = object
    code: seq[Instr]
    locals: seq[tuple[typ: TypeKind, used: bool]]
    map: Table[Value[Symbol], uint32]

  proc instr(c: var Assembler, op: Opcode) =
    c.code.add Instr(InstrType(op))
  proc instr(c: var Assembler, op: Opcode, a: int32) =
    c.code.add Instr(InstrType(op) or (a.InstrType shl instrAShift))
  proc instr(c: var Assembler, op: Opcode, b: uint16) =
    c.code.add Instr(InstrType(op) or (b.InstrType shl instrBShift))

  proc label(c: Assembler): uint32 = c.code.len.uint32
  proc jump(c: var Assembler, op: Opcode): uint32 =
    c.code.add Instr(InstrType(op))
    result = c.code.high.uint32
  proc join(c: var Assembler, pos: uint32) =
    c.code[pos] = Instr(InstrType(c.code[pos].opcode))
  proc jump(c: var Assembler, op: Opcode, target: uint32) =
    c.code.add Instr(InstrType(op) or (InstrType(c.code.len.uint32 - target) shl instrAShift))

  proc allocLocal(c: var Assembler, typ: TypeKind): int32 =
    for i, it in c.locals.mpairs:
      if it.typ == typ and not it.used:
        it.used = true
        return i.int32

    c.locals.add (typ, true)
    result = c.locals.high.int32

  proc alloc(c: var Assembler, x: Symbol): int32 =
    result = c.allocLocal:
      case x.typ.kind
      of tkFloat, tkInt: x.typ.kind
      else:              tkInt

    if x.typ.kind == tkBlob:
      # allocate a stack slot
      c.instr(opcStackAlloc, x.typ.size)
      c.instr(opcPopLocal, result)

  proc free(c: var Assembler, loc: int32, x: Symbol) =
    c.locals[loc].used = false
    if x.typ.kind == tkBlob:
      c.instr(opcStackFree, x.typ.size)

  proc expr(n: src.e, c: var Assembler) =
    match n:
    of Prim(t, str, e):
      case str.val
      of "+":
        expr(e[0], c)
        expr(e[1], c)
        c.gen(opcAddInt)
      of "<":
        expr(e[0], c)
        expr(e[1], c)
        c.gen(opcLtInt)
      of "<=":
        expr(e[0], c)
        expr(e[1], c)
        c.gen(opcLeInt)
      of "==":
        expr(e[0], c)
        expr(e[1], c)
        c.gen(opcEqInt)
    # of AddChecked(t, e0, e1, x):
    #   expr(e0, c)
    #   expr(e1, c)
    #   c.instr(opcAddChck)
    #   c.instr(opcPopLocal, x.get)
    of Addr(x):
      c.instr(opcGetLocal, x)
    of Let(s, e):
      let x = c.alloc(s)
      expr(e, c)
      c.free(x)
    of Load(t, e):
      expr(e)
      c.gen(opcLdInt32)
    of x:
      c.gen(opcGetLocal, c.map[x])
    of Call(t, s, e):
      for it in e.items:
        expr(it)
      c.gen(opcCall, s, x)
    of Exprs(st, e):
      for it in st.items:
        stmt(it, c)
      expr(e, c)

  proc stmt(n: src.st, c: var Assembler) =
    match n:
    of Let(s, st):
      let x = c.alloc(s.val)
      stmt(st, c)
      c.free(x, s.val)
    of If(e, st0, st1):
      expr(e, c)
      let x = c.jump(opcBranch)
      stmt(st0, c)
      let y = c.jump(opcJmp)
      c.join(x)
      stmt(st1, c)
      c.join(y)
    of If(e, st):
      expr(e, c)
      let x = c.jump(opcBranch)
      stmt(st, c)
      c.join(x)
    of While(e, st):
      let lab = c.label()
      expr(e, c)
      let x = c.jump(opcBranch)
      stmt(st, c)
      c.jump(opcJmp, lab)
      c.join(x)
    of Asgn(s, e):
      expr(e, c)
      c.instr(opcPopLocal, c.map[s])
    of Store(e0, e1):
      expr(e0, c)
      expr(e1, c)
      c.instr(opcWrInt16)
    # of MemCopy(e0, e1, e2):
    #   expr(e0)
    #   expr(e1)
    #   expr(e2)
    #   c.gen(opcMemCopy)
    of Return(e):
      expr(e, c)
      c.instr(opcRet)
    of Call(t, s, e1):
      for it in e1.items:
        expr(it, c)
      if s.val.typ.kind == tkPtr:
        c.instr(opcGetLocal, c.map[s])
        c.instr(opcIndCall, e1.len)
      else:
        c.instr(opcCall, s.val, e1.len)
    of Unreachable():
      c.instr(opcUnreachable)

  proc prc(name: src.x, ret: src.t, params: src.pa, body: src.st, m: var VmModule) =
    var c = Assembler()
    let p = unpack(params)
    for i, it in p.pairs:
      let loc = c.alloc(it.typ)
      c.locals[it] = loc
      c.instr(opcPopLocal, loc)
    stmt(body, c)
    # TODO: append to the module

  proc module(n: src.m, m: var VmModule): string =
    let procs = unpack(n)
    for it in procs.items:
      let (x, t, pa, s) = unpack(it)
      prc(x, t, pa, s, m)

  module(x, result)
]#

import std/macros

macro defineCompiler(name, names: untyped) =
  ## Generates a compiler procedures, running the provided passes in
  ## sequence. Interim implementation.
  var prev = ident"e"
  let body = newStmtList()
  for it in names.items:
    let tmp = genSym()
    if it.kind == nnkIdent:
      let name = it.strVal
      body.add quote do: echo "-- ", `name`
      body.add newLetStmt(tmp, quote do: `it`(`prev`, NodeIndex(0)))
    else:
      let g = it
      g.insert 1, quote do: NodeIndex(0)
      g.insert 1, prev
      let name = it[0].strVal
      body.add quote do: echo "-- ", `name`
      body.add newLetStmt(tmp, g)
    prev = tmp
  result = quote do:
    proc `name`(e: Ast[Lsrc]): auto =
      `body`
      result = `prev`

# some logic for testing:
var rep = initDefaultReporter[string]()
defineCompiler compile, [
  removeAndOr,
  removeSingleIf,
  declToLet,
  symbolize(rep),
  typeCheck,
  specializeAs,
  lowerMatch,
  nounion,
  norecord,
  bridge,
  simplifyLet,
  exprToStmt,
  ifExprToStmt,
  blobify,
  calleeToSymbol]

var s: SexpParser
# s.open(newStringStream("""
# (proc a (bool) () (exprs (decl x true) (decl y (and x 2)) (and (or 1 2) (and 3 4))))
# """))
s.open(newStringStream("""
(proc a (bool) ((x (int))) (== x 2))
(proc b (bool) ((x (float))) (== x 2))
(proc test (bool) ((x (union (int) (float)))) (match x (rule (y (int)) (a x)) (rule (z (float)) (b z))))
(proc main (bool) () (test (as 1 (union (int) (float)))))
"""))
discard s.getTok()
let m = parse(s)
s.close()

let got = compile(m)
