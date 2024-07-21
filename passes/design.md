## Nanopass Architecture

The idea is to structure compilation as repeatedly transforming the source
language into increasingly lower-level, well-defined intermediate languages
until the *target language* (or a language very close to it) is reached.

Except for the top-level language, intermediate languages are defined as an
*extension* of a higher-level intermediate language. A *pass* is responsible
for *lowering* an intermediate language into another one. Extensions are
intended to be very small, only focusing on one small feature or aspect, hence
the name *nano*pass.

Inspiration for the nanopass design was taken from
[Racket](https://docs.racket-lang.org/nanopass/index.html).

### Intermediate Language Definition

The semantics and grammar of a language are defined in a `langX.md` Markdown
file, which is accompanied by a `passX.nim` file implementing the actual pass.
The grammar of a language is provided by one or more Markdown code-blocks
using `grammar` as the language, and the definition's grammar is as follows:

```
Identifier ::= [a-zA-Z] [a-zA-Z0-9_]*
Reference ::= '<' Identifier '>'

RuleCore ::= SexpMatcher | Reference | (Identifier ':' Rule)
Rule ::= RuleCore ('*' | '+' | '?')?
SexprRule ::= '(' Identifier Rule* ')'

TopRule = Reference | SexprRule

Def ::= Identifier '::=' TopMatcher ('|' TopMatcher)*
Append ::= Identifier '+=' TopMatcher ('|' TopMatcher)*
Remove ::= Identifier '-=' TopMatcher ('|' TopMatcher)*

Top ::= ('.extends' Identifier)? (Def | Append | Remove)*
```

A `Def` defines a named rule, an `Append` appends to an existing named rule,
and a `Remove` removes the given rule(s) from the named rule. A `Reference`
is a reference to another named rule. There are two special references: `<int>`
and `<float>`. They refer to a literal integer and float value, respectively.

The idea is to use S-expressions as the serialization format (it's both human
readable and writable); basing the language definition on S-expressions
therefore also describes the serialization format.
