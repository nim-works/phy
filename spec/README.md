This directory provides tools for writing formal programming language
definitions.

At the core is a declarative meta-language that describes programming languages
as a set of named patterns (non-terminals), meta functions (i.e., functions
operating on meta-terms), and inductively-defined boolean relations (between
meta-terms).

[[langdefs.nim]] provides a macro DSL for conveniently constructing such
language definitions at compile time.

At the moment, the meta-language has no formal definition itself. The macro
DSL is currently the most accurate reference for what's valid and what's not.
Not everything that's disallowed in the meta-language is rejected by the
macro, so watch out.
