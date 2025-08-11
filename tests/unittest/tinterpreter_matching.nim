discard """
  description: "Tests for the pattern matching of the meta-language interpreter"
"""

import std/[importutils, tables]
import spec/cps
import spec/interpreter {.all.}
import spec/types except Node

# some procs/types to make writing tests easier

type Node = types.Node[TypeId]

template sym(n: string): Node = Node(kind: nkSymbol, sym: n)
template hole(): Node = Node(kind: nkHole)
template ctxRef(i: int): Node = Node(kind: nkContext, id: i)
template vid(i: int): Node = Node(kind: nkVar, id: i)
template capture(i: int): Node = tree(nkBind, vid(i))
template capture(i: int, pat: Node): Node = tree(nkBind, vid(i), pat)
proc constr(head: string, ops: varargs[Node]): Node =
  result = tree(nkConstr, sym(head))
  result.children.add ops

proc `==`(a, b: Node): bool =
  if a.kind == b.kind:
    case a.kind
    of nkSymbol, nkString:
      a.sym == b.sym
    of nkNumber:
      a.num == b.num
    of nkFunc, nkRelation, nkVar, nkContext:
      a.id == b.id
    of withChildren:
      a.children == b.children
    else:
      true
  else:
    false

proc patterns(pat: varargs[seq[Node]]): LangDef =
  for it in pat.items:
    result.matchers.add Pattern[TypeId](patterns: it)

proc all(lang: LangDef, pat, term: Node): seq[Bindings] =
  privateAccess(Match)
  var m = matches(lang, pat, term)
  while m.has:
    result.add m.bindings
    if m.alt.isNil:
      m = default(Match)
    else:
      m = m.alt(lang)

proc test(lang: LangDef, pat, term: Node, expect: openArray[Bindings]) =
  # the order of `expect` is not significant
  var got = all(lang, pat, term)
  var i = 0
  var error = false
  for it in expect.items:
    let i = got.find(it)
    if i == -1:
      echo "no match producing set '", it, "'"
      error = true
    else:
      got.del(i)

  if got.len > 0:
    for it in got.items:
      echo "match has extraneous binding: ", it
    error = true

  if error:
    raise CatchableError.newException("test failed")

# --------------------
# ------ tests -------
# --------------------

block hole_in_list:
  let lang = patterns(@[constr("a", hole())])
  test(lang,
    tree(nkPlug, capture(0, ctxRef(0)), capture(1)),
    constr("a", sym"b"),
    [toTable {0: constr("a", hole()), 1: sym"b"}]
  )

block recursive_pattern:
  var lang = patterns(@[
    hole(),
    constr("a", ctxRef(0))
  ])
  # simple symbol
  test(lang,
    tree(nkPlug, capture(0, ctxRef(0)), capture(1)),
    sym"b",
    [toTable {0: hole(), 1: sym"b"}]
  )
  # simple list
  test(lang,
    tree(nkPlug, capture(0, ctxRef(0)), capture(1)),
    constr("a", constr("a", sym"b")),
    [
      toTable {0: hole(), 1: constr("a", constr("a", sym"b"))},
      toTable {0: constr("a", hole()), 1: constr("a", sym"b")},
      toTable {0: constr("a", constr("a", hole())), 1: sym"b"}
    ]
  )

block mutually_recursive_patterns:
  let lang = patterns(
    @[constr("b", ctxRef(1))],
    @[hole(),
      constr("a", ctxRef(0))]
  )
  test(lang,
    tree(nkPlug, capture(0, ctxRef(1)), capture(1)),
    constr("a", sym"b"),
    [toTable {0: hole(), 1: constr("a", sym"b")}]
  )

  test(lang,
    tree(nkPlug, capture(0, ctxRef(1)), capture(1)),
    constr("a", constr("b", sym"c")),
    [
      toTable {0: hole(), 1: constr("a", constr("b", sym"c"))},
      toTable {0: constr("a", constr("b", hole())), 1: sym"c"}
    ]
  )

block plug_in_plug:
  # plug pattern used as the plugged-with pattern
  let lang = patterns(@[
    hole(),
    constr("a", ctxRef(0))
  ])
  test(lang,
    tree(nkPlug, capture(0, ctxRef(0)), tree(nkPlug, capture(1, ctxRef(0)), capture(2))),
    constr("a", constr("a", constr("a", sym"b"))),
    [
      toTable {0: hole(), 1: hole(), 2: constr("a", constr("a", constr("a", sym"b")))},
      toTable {0: hole(), 1: constr("a", hole()), 2: constr("a", constr("a", sym"b"))},
      toTable {0: hole(), 1: constr("a", constr("a", hole())), 2: constr("a", sym"b")},
      toTable {0: hole(), 1: constr("a", constr("a", constr("a", hole()))), 2: sym"b"},
      toTable {0: constr("a", hole()), 1: hole(), 2: constr("a", constr("a", sym"b"))},
      toTable {0: constr("a", hole()), 1: constr("a", hole()), 2: constr("a", sym"b")},
      toTable {0: constr("a", hole()), 1: constr("a", constr("a", hole())), 2: sym"b"},
      toTable {0: constr("a", constr("a", hole())), 1: hole(), 2: constr("a", sym"b")},
      toTable {0: constr("a", constr("a", hole())), 1: constr("a", hole()), 2: sym"b"},
      toTable {0: constr("a", constr("a", constr("a", hole()))), 1: hole(), 2: sym"b"},
    ]
  )

block nested_plug_pattern:
  # a plug pattern part of a context / named pattern
  var lang = patterns(
    @[constr("A", hole()),
      constr("B", hole())],
    @[hole(),
      constr("C", hole()),
      tree(nkPlug, ctxRef(0), ctxRef(1))]
  )
  test(lang,
    tree(nkPlug, capture(0, ctxRef(1)), capture(1)),
    constr("A", constr("B", constr("C", sym"test"))),
    [
      toTable {0: hole(), 1: constr("A", constr("B", constr("C", sym"test")))},
      toTable {0: constr("A", hole()), 1: constr("B", constr("C", sym"test"))},
      toTable {0: constr("A", constr("B", hole())), 1: constr("C", sym"test")},
      toTable {0: constr("A", constr("B", constr("C", hole()))), 1: sym"test"},
    ]
  )

block hole_after_repetition:
  let lang = patterns(
    @[constr("a", tree(nkZeroOrMore, sym"b"), hole(), tree(nkZeroOrMore, sym"b"))]
  )
  # note: zero-or-more patterns only yield at most one match
  test(lang,
    tree(nkPlug, capture(0, ctxRef(0)), capture(1)),
    constr("a", sym"b", sym"b", sym"b"),
    [toTable {0: constr("a", sym"b", sym"b", hole()), 1: sym"b"}]
  )

block hole_in_repetition:
  let lang = patterns(
    @[constr("a", tree(nkZeroOrMore, hole()))]
  )
  test(lang,
    tree(nkPlug, capture(0, ctxRef(0)), capture(1)),
    constr("a", sym"b", sym"c"),
    [
      toTable {
        0: tree(nkGroup, constr("a", hole(), sym"c"), constr("a", sym"b", hole())),
        1: tree(nkGroup, sym"b", sym"c")
      }
    ]
  )
