## Implements a code generator that produces syntax checks based on an input
## ``Grammar``.

import
  std/[
    macros,
    tables
  ],
  grammar

type
  Output = object
    text: string
    indent: int

macro addCode(s: var string, code: untyped) =
  ## Renders `code` to text and appends the result to `s`.
  let str = newLit repr(code)
  result = quote:
    `s`.add `str`

proc add(o: var Output, m: string) =
  for _ in 0..<o.indent:
    o.text.add "  "
  o.text.add m

proc short(e: Expr): string =
  ## Produces a shorter text representation of `e` than ``$``.
  assert not e.isRef
  result = "(" & e.name
  for it in e.rules.items:
    result.add " "
    if it.expr.isRef:
      result.add "<" & it.expr.name & ">"
    else:
      result.add "(" & it.expr.name
      if it.expr.rules.len > 0:
        result.add " ..."
      result.add ")"

    case it.repeat
    of rOnce:       discard
    of rZeroOrOne:  result.add "?"
    of rZeroOrMore: result.add "*"
    of rOneOrMore:  result.add "+"

  result.add ")"

proc genMatcher(e: Expr, output: var Output): string =
  ## Generates the matcher code for the single expression `e`. Returns the
  ## boolean expression to test for success with.
  if e.isRef:
    if e.name in ["int", "float", "string"]:
      # ``Immediate`` is only really valid for int, but the other two are
      # expected to never be executed anyway
      result = "matchAtom(tree, n, Immediate)"
    else:
      result = "check_" & e.name & "(tree, n, err)"
  else:
    output.add "matchTree \"" & short(e) & "\", " & e.name & ", match:\n"
    inc output.indent

    var hasTmp = false

    for i, m in e.rules.pairs:
      case m.repeat
      of rOnce:
        let x = genMatcher(m.expr, output)
        output.add "if num == len or not " & $x & ": break match\n"
        output.add "inc num\n"
      of rZeroOrOne:
        let x = genMatcher(m.expr, output)
        output.add "if num < len and " & x & ": inc num\n"
      of rZeroOrMore:
        output.add "while num < len:\n"
        inc output.indent
        output.add "if not " & genMatcher(m.expr, output) & ": break\n"
        output.add "inc num\n"
        dec output.indent
      of rOneOrMore:
        if hasTmp:
          output.add "tmp = num\n"
        else:
          output.add "var tmp = num\n"
          hasTmp = true

        output.add "while num < len:\n"
        inc output.indent
        output.add "if not " & genMatcher(m.expr, output) & ": break\n"
        output.add "inc num\n"
        dec output.indent
        output.add "if tmp == num: break match\n"

    if e.rules.len == 0:
      output.add "discard\n"

    dec output.indent
    result = "result"

proc gen*(lang: Grammar, module: string): string =
  result = "# Generated by the passtool; do not modify\n"
  result.add "import passes/trees\n"
  result.add "import " & module & "\n"
  # emit some types and routines that make code generation easier and reduce
  # the size of the output (at the cost of slightly more work for the
  # compiler)
  result.addCode:
    type
      Tree = PackedTree[NodeKind]
      Error = object
        pos: NodeIndex # error position

        rule: string
        node: NodeIndex # position of the error's parent node
        child: int

    template setError(e, n: NodeIndex, c: int, r: string) =
      if ord(err.pos) < ord(e):
        err = Error(pos: e, rule: r, node: n, child: c)

    proc matchAtom(tree: Tree, n: var NodeIndex, kind: NodeKind): bool =
      result = n in tree and tree[n].kind == kind
      if result: n = tree.next(n)

    template matchTree(rule: string, k: NodeKind, label, body: untyped) =
      # the grammar doesn't know which nodes are atoms, and it thus has to
      # delegate the decision to the ``isAtom`` procedure
      when isAtom(k):
        result = matchAtom(tree, n, k)
      else:
        if n in tree and tree[n].kind == k:
          let save = n
          let len {.inject.} = tree.len(n)
          var num {.inject.} = 0
          var success = false
          n = tree.child(n, 0)
          block label:
            body
            success = num == len

          result = success
          if not result:
            setError n, save, num, rule
            n = save # restore the start position
        else:
          result = false

  result.add "\n"

  # emit a check procedure for each named rule:
  var defs = Output()
  for name, prods in lang.pairs:
    # to simplify code generation, all check procedures have a forward
    # declaration
    result.add:
      "proc check_" & name & "*(tree: Tree, n: var NodeIndex, err: var Error): bool\n"

    defs.add "proc check_" & name & "*(tree: Tree, n: var NodeIndex, err: var Error): bool =\n"
    inc defs.indent
    # emit the matching logic for each production. The check procedure
    # returns 'true' as soon as one succeeds, 'false' if none does
    for p in prods.items:
      let e = genMatcher(p.expr, defs)
      defs.add "if " & e & ": return true\n"

    dec defs.indent
    defs.add "\n"

  result.add "\n"
  result.add defs.text

  # emit the convenience wrapper:
  result.addCode:
    template check*(tree: Tree, n: NodeIndex, name, onErr: untyped) =
      if true:
        var
          error: Error
          node = n
        if not `check name`(tree, node, error):
          let
            rule {.inject, used.} = error.rule
            node {.inject, used.} = error.node
            child {.inject, used.} = error.child
          onErr
