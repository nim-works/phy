
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

Glossary
--------

record
  a heterogeneous map from names to values, whose shape (number of entries and
  their names and types) is fixed

terminal
  in the context of the nanopass framework, a type that's defined outside a
  language. This corresponds to a terminal in a formal grammar, hence the name

form
  a named schema for a term. Can also be viewed as a named tuple

production
  either a form, a record, or a terminal

non-terminal
  a set of productions

meta-variable
  ranges over the terms a type. In the nanopass framework, they're mostly
  just short-hands for types

language
  a collection of terminals, records, and forms, plus the non-terminals for
  connecting them together

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

  The type bound to the identifier is not meant to be used as a type for
  values. Rather, it acts as a namespace through which entities defined in the
  language are accessed.

The body consists of a sequence of terminal, record, and non-terminal definitions.

.. code-block:: nim
    :test: "nim c $1"

  import nanopass/nanopass

  defineLanguage L0:
    int(i)                 # definition of a terminal
    rec(r)  ::= (field: i) # definition of a record
    expr(e) ::= i          # definition of a non-terminal

  # this defines a language `L0` with:
  # * a terminal of type `int`, ranged over by meta-variable `i`
  # * a record type with name `rec`, ranged over by meta-variable `r`. The
  #   record has a single field called `field`, whose values must be of
  #   type `int`
  # * a non-terminal with name `expr`, ranged over by meta-variable `e`. Where
  #   this non-terminal is expected, there must be value of type `int`

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

No two non-terminals may have the same name.

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    int(i)
    expr(e) ::= i
    expr(b) ::= i # error: 'expr' name already in use

All types share the same namespace.

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    int(i)
    int(e) ::= i # a type with name 'int' already exists

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    int(i)
    int(e) ::= (field: i) # a type with name 'int' already exists

Types and meta-variables also share a namespace, meaning that it's not
possible to give a name to a type already used for a meta-variable,
and vice versa.

.. code-block:: nim
    :test: "nim c $1"
    :status: 1

  import nanopass/nanopass

  defineLanguage L0:
    int(i)
    i(e) ::= i # error: 'i' already in use


For terminal types, the name refer to a NimSkull type that exists at the time
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
