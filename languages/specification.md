## Phy Specification

An outdated document previously providing the authoritative definition of the
source language. It only contains the grammar for source language's abstract
syntax (which is still needed by the passtool).

> Note: this will be eventually made obsolete by the passtool being removed

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
