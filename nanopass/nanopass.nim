## Implements the nanopass framework, which is a collection of macro DSLs for
## defining intermediate languages (their syntax and grammar) and passes.

# TODO:
# * implement types integration
# * implement meta-data support
# * add a "compiler definition" macro

import
  nanopass/[asts, nplanggen, npmatch, npbuild, npparser, nppass, nppatterns, npunparser]

export asts
export nppatterns.matches
export npbuild.build, npmatch.match, npunparser.unparse, npparser.parseAst
export nppass.pass, nppass.inpass, nppass.outpass
export nppass.get

macro defineLanguage*(name, body: untyped) =
  ## Creates a language definition and binds it to a const symbol with the
  ## given name.
  defineLanguageImpl(name, nil, body)

macro defineLanguage*(name, base, body: untyped) =
  ## Creates a language definition, extending `base`, and binds it to a const
  ## symbol with the given name. Extension doesn't imply a direction in this
  ## context.
  defineLanguageImpl(name, base, body)
