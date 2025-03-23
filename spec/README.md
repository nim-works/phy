This directory provides tools for writing formal programming language
definitions.

The center piece is a meta language with features tailored to describing/
modeling programming language semantics (both static, dynamic, and everything
in-between). An overview of the meta language can be found in the
[manual](manual.md).

The core modules are:
* [langdefs](langdefs.nim):
  implements the semantic analysis for the meta language. A macro DSL provides
  the frontend and syntax
* [interpreter](interpreter.nim):
  a simple interpreter for evaluating meta-language terms

At the moment, the meta-language has no formal definition itself.
