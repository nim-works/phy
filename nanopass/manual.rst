
Nanopass Framework
==================

This document describes how to use the nanopass framework, what is allowed, and
what not. It only describes the framework's interface, not how things are
implemented internally.

Nanopass Compiler Overview
--------------------------

A nanopass compiler is a compiler implemented as a series of narrow *passes*,
which *transform*, *analyze*, or otherwise produce abstract syntax trees (=AST)
according to well-defined grammars.

The idea is that passes focus on small, specific tasks, with tree traversal
boilerplate generated automatically.

Concepts
--------

* a *language* (in the context of the nanopass framework) is a formal grammar.
* a *terminal* is ...
* a *form* is a named schema for a term, made up of zero or more sub-terms
* a *non-terminal* is ...
* a *meta-variable* is a name ranging over a terminal or non-terminal. It may be viewed as an alias.

.. TODO rewrite this section. It should use the correct terminology while still
        being approachable to someone not overly familiar with formal grammars

Usage
-----

Language Definition
~~~~~~~~~~~~~~~~~~~

Languages are defined via the `defineLanguage` macro, which has two forms.

From Scratch
~~~~~~~~~~~~

The first form `defineLanguage` form takes two arguments, an identifier and
a body, and defines a language from scratch. If the body is valid, a NimSkull
type is bound to the identifier.

.. note::

  The type is not meant to be used as a type for values. Rather, it
  acts as a namespace through which entities defined in the language are
  accessed.

The body consists of a sequence of terminal and non-terminal definitions.

.. code-block:: nim
    :test: "nim c $1"

  import nanopass/nanopass

  defineLanguage L0:
    int(i)         # definition of a terminal
    expr(e) ::= i  # definition of a non-terminal

  # this defines a language `L0` with:
  # * a single terminal of type `int`, ranged over by meta-variable `i`
  # * a non-terminal with name `expr`, ranged over by meta-variable `e`. Where
  #   this non-terminal is expected, an `int` value is allowed

Meta-variables must be unique.

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    int(i)
    float(i) # error: 'i' name already in use

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    int(i)
    integer(i) ::= i # error: 'i' name already in use

All meta-variables defined in the body are accessible in all non-terminals,
regardless of the declarations' order.

.. code-block:: nim
    :test: "nim c $1"

  import nanopass/nanopass

  defineLanguage L0:
    expr(e) ::= i
    int(i)

Each non-terminals must have a unique name.

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    int(i)
    expr(e) ::= i
    expr(b) ::= i # error: 'expr' name already in use

Non-terminals and meta-variables share a namespace, meaning that it's not
possible to give a name to a non-terminal already used for a meta-variable,
and vice versa.

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    int(i)
    i(e) ::= i # error: 'i' already in use

For terminals, the type expression must be an identifier, more complex
expressions are not allowed.

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    (ref int)(i) # error: not an identifier
    expr(e) ::= i

The identifier must also refer to a type that exists at the time
`defineLanguage` is expanded.

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    MyType(i)
    expr(e) ::= i

  type MyType = object # too late, must be defined before the language

.. TODO continue

Define Language Via Difference
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The second form of `defineLanguage` takes takes three arguments, two
identifiers and a body, and defines a language by applying the diff provided
by the body to the base language. If the result is valid, a NimSkull
type is bound to the identifier.

The second argument must be the name of an in-scope identifier to which a
language definition was previously bound via `defineLanguage`.

.. TODO continue

AST
---

.. TODO continue

Pattern Matching
----------------

The nanopass framework provides a facility for comprehending AST fragments
using pattern matching, via the `match` routine.

.. TODO continue

Passes
------


.. TODO continue

The `build` Form
~~~~~~~~~~~~~~~~

Passes that produce an AST have a special macro available within their body:
the `build` macro. It's used to create AST fragments in a statically type-safe
manner.

.. TODO continue

Value To Language
~~~~~~~~~~~~~~~~~

.. TODO continue

Language To Language
~~~~~~~~~~~~~~~~~~~~

.. TODO continue

Language To Value
~~~~~~~~~~~~~~~~~

.. TODO continue
