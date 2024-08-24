## Source Language

The highest-level language. At the moment, the grammar describes the grammar
of the parse-tree, not the grammar of the textual representation (i.e., how
the parse-tree is constructed from tokens).

```grammar
ident ::= (Ident <string>)

expr ::= (IntVal <int>)
      |  (FloatVal <float>)
      |  (Call <ident> <expr>*)
```
