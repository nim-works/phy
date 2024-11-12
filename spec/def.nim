## Provides the formal definition for Phy.

language "source":
  grammar:
    ident     = (Ident, $str)
    int_val   = (IntVal, $i)
    float_val = (FloatVal, $f)

    local_decl = (Decl, ident, expr)

    expr =  int_val    or
            float_val  or
            ident      or
            local_decl or
            (Return, ?expr)     or
            (Unreachable)       or
            (Exprs, +expr)      or
            (And,  expr, expr)  or
            (Or,   expr, expr)  or
            (Asgn, expr, expr)  or
            (TupleCons)         or
            (TupleCons, +expr)  or
            (Call, expr, *expr) or
            (If, expr, expr, ?expr) or
            (FieldAccess, expr, int_val)

    type_expr = (VoidTy)      or
                (UnitTy)      or
                (BoolTy)      or
                (IntTy)       or
                (FloatTy)     or
                (Ident, $str) or
                (TupleTy)     or
                (TupleTy, +type_expr) or
                (UnionTy, +type_expr) or
                (ProcTy, type_expr, *type_expr)

    decl =  (ProcDecl, ident, type_expr, (Params), expr) or
            (TypeDecl, ident, type_expr)

    module = (Module, decl)
    top    = module

  derived "and":
    And(e1, e2) -> If(e1, e2, Ident("false"))

  derived "or":
    Or(e1, e2) -> If(e1, Ident("true"), e2)

  derived "single expression":
    Exprs(e) -> e

  semantics "expressions":
    rule "int":
      var C: any
      then C, IntVal, (C, int)

    rule "float":
      var C: any
      then C, FloatVal, (C, float)

    rule "_":
      var C: any
      then C, Ident("false"), (C, bool)

    rule "_":
      var C: any
      then C, Ident("true"), (C, bool)

    rule "mutable variable":
      var C, T, k, name: any
      then C, Ident(name), (C, mut(T))
      condition C.vars(name) == (T, k)
      condition k == mut

    rule "immutable variable":
      var C, T, k, name: any
      then C, Ident(name), (C, T)

      condition C.vars(name) == (T, k)
      condition k != mut

    rule "expression list":
      var C, T, e: seq
      var i: range
      var C_last, T_last, e_last: any
      then C[0], Exprs(e[], e_last), (C_last, T_last)
      condition T[i] == unit
      hypothesis C[i],  e[i],   (C[i+1], all T[i])
      hypothesis C[^1], e_last, (C_last, all T_last)

    rule "single-branch if":
      var C, C1, T1, T2, e1, e2: any
      then C, If(e1, e2), (C, unit)
      condition T1 == bool
      condition T2 in {unit, void}
      hypothesis C,  e1, (C1, all T1)
      hypothesis C1, e2, (_,  all T2)

    rule "if":
      var C, C1, T1, T2, T3, R, e1, e2: any
      then C, If(e1, e2, e3), (C1, R)
      condition T1 == bool
      condition common(T2, T3) == R
      condition R != undefined
      hypothesis C,  e1, (C1, all T1)
      hypothesis C1, e2, (_,  all T2)
      hypothesis C1, e3, (_,  all T3)

    rule "field access":
      var C, e, i, C1, T: any
      then C, FieldAccess(e, IntVal(i)), (C1, T)
      condition T is tuple
      condition n in T
      hypothesis C, e, (C1, T)

    rule "mutable field access":
      var C, e, i, C1, T: any
      then C, FieldAccess(e, IntVal(i)), (C1, mut T)
      condition T is tuple
      condition n in T
      hypothesis C, e, (C1, mut T)

    rule "unit constructor":
      var C: any
      then C, TupleCons(), (C, unit)

    rule "multi-element tuple constructor":
      var C, T, e: seq
      var i: range
      then C[0], TupleCons(e[]), (C[^1], `tuple`(T[]))
      condition T[i] != void
      hypothesis C[0], e[i], (C[i+1], all T[i])

    rule "return":
      var C, T, e: any
      then C, Return(e), (C, void)
      # the context resulting from the expression is discarded
      condition common(T, C.ret) == C.ret
      hypothesis C, e, (C, all T)

    rule "empty return":
      var C, T, e: any
      then C, Return(), (C, void)
      condition common(unit, C.ret) == C.ret

    rule "unreachable":
      var C, T, e: any
      then C, Unreachable(), (C, void)

    rule "assignment":
      var C, C1, C2, e1, e2, T1, T2: any
      then C, Asgn(e1, e2), (C2, unit)
      condition common(T1, T2) == T1
      hypothesis C,  e1, (C1, mut T1)
      hypothesis C1, e2, (C2, all T2)

    rule "+":
      var C, C1, C2, T, e1, e2: any
      then C, Call(Ident("+"), e1, e2), (C2, T)
      condition T in {int, float}
      hypothesis C,  e1, (C1, all T)
      hypothesis C1, e2, (C2, all T)

    rule "-":
      var C, C1, C2, T, e1, e2: any
      then C, Call(Ident("-"), e1, e2), (C2, T)
      condition T in {int, float}
      hypothesis C,  e1, (C1, all T)
      hypothesis C1, e2, (C2, all T)

    rule "<":
      var C, C1, C2, T, e1, e2: any
      then C, Call(Ident("<"), e1, e2), (C2, bool)
      condition T in {int, float}
      hypothesis C,  e1, (C1, all T)
      hypothesis C1, e2, (C2, all T)

    rule "<=":
      var C, C1, C2, T, e1, e2: any
      then C, Call(Ident("<="), e1, e2), (C2, bool)
      condition T in {int, float}
      hypothesis C,  e1, (C1, all T)
      hypothesis C1, e2, (C2, all T)

    rule "==":
      var C, C1, C2, T, e1, e2: any
      then C, Call(Ident("=="), e1, e2), (C2, bool)
      condition T in {int, float}
      hypothesis C,  e1, (C1, all T)
      hypothesis C1, e2, (C2, all T)

    rule "not":
      var C, C1, T, e: any
      then C, Call(Ident("not"), e), (C1, T)
      condition T == bool
      hypothesis C, e, (C1, all T)

    rule "procedure call":
      var C, C1, C1, T, R, callee: any
      then C, Call(callee), (C1, R)
      hypothesis C, callee, (Ca[0], all `proc`(R))

    rule "procedure call":
      var C, C1, R, callee: any
      var Ca, T, e: seq
      var i: range
      then C, Call(callee, e[]), (Ca[^1], R)
      hypothesis C,    callee, (Ca[0],   all `proc`(R, T[]))
      hypothesis C[i], e[i],   (Ca[i+1], all T[0])

    rule "decl":
      var C, C1, T, e: any
      then C, Decl(Ident(name), e), (C1 + ({name: (T, mut)}, {}), unit)
      # XXX: declarations should use a dedicated type instead of `unit`
      condition name notin C1.vars
      hypothesis C, e, (C1, all(T))

  semantics "type expressions":
    rule "identifier":
      var C, T, name: any
      then C, Ident(name), (C, T)
      condition C.types(name) == T
      condition T != undefined

    rule "":
      var C: any
      then C, IntTy, (C, int)

    rule "":
      var C: any
      then C, FloatTy, (C, float)

    rule "":
      var C: any
      then C, UnitTy, (C, unit)

    rule "":
      var C: any
      then C, VoidTy, (C, void)

    rule "empty tuple":
      var C: any
      then C, TupleTy, (C, unit)

    rule "tuple":
      var C: any
      var T, t: seq
      var i: range
      then C, TupleTy(t[]), (C, `tuple`(T[]))
      condition T[i] != void
      hypothesis C, t[i], (C, T[i])

    rule "union":
      var C: any
      var T, t: seq
      then C, UnionTy(t[]), (C, union(T[]))
      # TODO: uniqueness requirement is missing
      condition T[i] != void
      hypothesis C, t[i], (C, T[i])

    rule "nullary proc type":
      var C, T, t: any
      then C, ProcTy(t), (C, `proc`(T))
      hypothesis C, t, (C, T)

    rule "proc type":
      var C, R, t: any
      var P, tp: seq
      var i: range
      then C, ProcTy(t, tp[]), (C, `proc`(R, P[]))
      condition P[i] != void
      hypothesis C, t, (C, R)
      hypothesis C, tp[i], (C, P[i])

  semantics "top-level declarations":
    rule "proc declaration":
      var C, t, T, R, name, e, C1: any
      then C, ProcDecl(name, t, Params(), e), C1
      condition C.vars(name) == undefined
      condition R == void
      condition C1 == C + ({name: (`proc`(T), imm)}, {})
      hypothesis C,  t, (_, T)
      hypothesis C1, e, (_, R)

    rule "type declaration":
      var C, T, t, name: any
      then C, TypeDecl(Ident(name), t), C + ({}, {name: T})
      condition C.types(name) == undefined
      hypothesis C, t, (_, T)

  semantics "modules":
    rule "empty module":
      var C: any
      then C, Module, C

    rule "module":
      var C, d: seq
      var i: range
      then C[0], Module(d[]), C[^1]
      hypothesis C[i], d[i], (C[i+1])
