## Phy Specification

This document describes the semantics of the source language.

A *program* consists of a single *module*. A *module* consists of zero or more
*declarations*.

A *declaration* introduces a new entity, one that can later be referred to with
the given name.

An *expression* is a term or a control-flow instruction. All expressions have a
*type*.

A *statement* is a computation without a type.

### Types

The built-in types (also referred to as "primitive types") are:
* `void`
* `unit`
* `int`
* `float`

`void` is the *empty type*, and functions as the *bottom type*. It is
uninhabited, meaning that there are no valid terms for it.

`unit` is a type that has only *one* value.

`int` is the type of signed integer values, where the size and range is target-
dependent.

`float` is the type of floating point values, where the size is target-
dependent.
