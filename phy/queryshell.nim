## Implements a simple command-line shell to query information from and run
## functions/relations from language definitions. Meant as a tool to aid with
## language development.

import
  std/[
    dynlib,
    options,
    os,
    osproc,
    strutils,
    sequtils,
    tables
  ],
  experimental/[
    sexp,
    colortext
  ],
  phy/sexpstreams,
  spec/[
    int128,
    interpreter,
    rationals
  ]

import spec/types except Node

type
  Node = types.Node[TypeId] # shorthand that's easier to write

const
  LoaderCode = """
import $1
proc load*(): auto {.cdecl, dynlib, exportc.} = addr lang
"""
    ## the program for loading the langdef. A pointer is returned in
    ## order to prevent a copy, which would be dangerous due to it
    ## using the library's own allocator instance (which the main
    ## program is not aware of)
  CompileCmd = "nim c --fromcmd --app:lib --path:. --verbosity:0 --o:$1 $2"
    ## the command to compile the loader with. Be as quiet as possible

# global state:
var
  vars: Table[string, Node]
  depth: int ## current cursor's depth
  prev: Node ## previous execution result
  langOpt: Option[LangDef] ## the currently loaded language definition

template lang: untyped = langOpt.unsafeGet

proc prepareMutation[T: not string](x: var T) =
  ## Copies the payload of all strings in `x` into heap memory. Used to
  ## "detach" the strings from the dynamic library into whose static memory
  ## the payload pointers point.
  when T is (object or tuple):
    for it in fields(x):
      when it isnot (enum or SomeInteger):
        prepareMutation(it)
  elif T is seq:
    for it in x.mitems:
      prepareMutation(it)
  else:
    discard

proc fromSexp(s: SexpNode): Node =
  ## Parses a meta-language expression from `s`.
  template fromList(kind: NodeKind): Node =
    tree(kind, map(toOpenArray(s.elems, 1, s.len-1), fromSexp))

  proc assoc(s: SexpNode): Node =
    if s.kind == SList and s.len == 2:
      tree(nkAssoc, fromSexp(s[0]), fromSexp(s[1]))
    else:
      raise ValueError.newException("two-element list expected")

  case s.kind
  of SList:
    if s.len == 0:
      raise ValueError.newException("non-empty list expected")
    elif s[0].kind != SSymbol:
      raise ValueError.newException("expected symbol")

    case s[0].symbol
    of ":tuple":
      fromList(nkTuple)
    of ":map":
      tree(nkMap, map(s.elems.toOpenArray(1, s.len-1), assoc))
    of ":rec":
      tree(nkRecord, map(s.elems.toOpenArray(1, s.len-1), assoc))
    of ":set":
      fromList(nkSet)
    elif s[0].symbol.startsWith(":"):
      raise ValueError.newException("unknown keyword: " & s[0].symbol)
    else:
      # must be a user-defined construction
      tree(nkConstr, map(s.elems, fromSexp))
  of SSymbol:
    if s.symbol.startsWith("$") and s.symbol.len > 1:
      let name = s.symbol[1..^1]
      vars.withValue name, it:
        return it[]
      do:
        raise ValueError.newException("no var with name " & name)
    elif s.symbol == ":true":
      Node(kind: nkTrue)
    elif s.symbol == ":false":
      Node(kind: nkFalse)
    else:
      Node(kind: nkSymbol, sym: s.symbol)
  of SInt:
    Node(kind: nkNumber, num: frac(toInt128(s.num), toInt128(1)))
  of SFloat:
    Node(kind: nkNumber, num: parseRational($s.fnum))
  of SString:
    Node(kind: nkString, sym: s.str)
  of SNil, SCons, SKeyword:
    raise ValueError.newException("unexpected expression")

proc add(res: var string, n: Node) =
  ## The inverse of ``fromSexp``, but without going through an intermediate
  ## ``SexpNode`` first.
  proc addList(res: var string, s: string, n: Node) =
    res.add "(" & s
    for it in n.children.items:
      res.add " "
      res.add it
    res.add ")"

  case n.kind
  of nkConstr, nkAssoc:
    res.add "("
    for i, it in n.children.pairs:
      if i > 0:
        res.add ' '
      res.add it
    res.add ")"
  of nkNumber:
    res.addRat n.num
  of nkSymbol:
    res.add n.sym
  of nkString:
    res.add escape(n.sym)
  of nkTuple:
    res.addList(":tuple", n)
  of nkSet:
    res.addList(":set", n)
  of nkMap:
    res.addList(":map", n)
  of nkRecord:
    res.addList(":rec", n)
  of nkTrue:
    res.add ":true"
  of nkFalse:
    res.add ":false"
  else:
    res.add "..."

proc `$`(n: Node): string =
  result.add(n)

proc getDefault(lang: LangDef, typ: TypeId): types.Node[TypeId] =
  ## Returns the default value for `typ`.
  case lang[typ].kind
  of tkInt, tkRat, tkAll:
    Node(kind: nkNumber, num: frac(toInt128(0), toInt128(1)), typ: typ)
  of tkBool:
    Node(kind: nkFalse, typ: typ)
  of tkVoid:
    Node(kind: nkFail, typ: typ)
  of tkFunc:
    if lang[lang[typ].children[1]].kind == tkBool:
      Node(kind: nkSet, typ: typ)
    else:
      Node(kind: nkMap, typ: typ)
  of tkTuple:
    var r = Node(kind: nkTuple, typ: typ)
    for it in lang[typ].children.items:
      r.add getDefault(lang, it)
    r
  of tkList:
    Node(kind: nkGroup, typ: typ)
  of tkRecord:
    var r = Node(kind: nkRecord, typ: typ)
    for it in lang[typ].fields.items:
      r.add tree(nkAssoc, Node(kind: nkSymbol, sym: it.name),
                 getDefault(lang, it.typ))
    r
  of tkData:
    var r: Node
    # find a nullary constructor
    for it in lang[typ].constr.items:
      if it.kind == nkSymbol or it.len == 1:
        r = it
        break
    r
  of tkSum:
    getDefault(lang, lang[typ].children[0])

proc pretty(res: var ColText, t: Trace, indent: int) =
  ## Pretty-prints the trace `t` and adds the result to `res`.
  res.add repeat("  ", indent)
  res.add "- "
  res.add lang.relations[t.id].name + fgCyan

  var ip, op, countIn, countOut = 0
  # count the number of inputs/outputs:
  for it in lang.relations[t.id].params.items:
    if it.input:  inc countIn
    else:         inc countOut

  # render the inputs and outputs:
  for it in lang.relations[t.id].params.items:
    res.add " "
    if it.input:
      if countIn == 1:
        res.add $t.input
      else:
        res.add $t.input[ip]
        inc ip
    else:
      if countOut == 1:
        res.add $t.output
      else:
        res.add $t.output[op]
        inc op

  res.add " | " + fgYellow
  res.add lang.relations[t.id].rules[t.rule].name + fgYellow

  for it in t.sub.items:
    res.add "\n"
    pretty(res, it, indent + 1)

proc pick(lang: LangDef, name: string): Node =
  # look through the relations
  for i, it in lang.relations.pairs:
    if it.name == name:
      return Node(kind: nkRelation, id: i)

  # no success; look through the functions
  for i, it in lang.functions.pairs:
    if it.name == name:
      return Node(kind: nkFunc, id: i)

  result = Node(kind: nkFail)

proc error(msg: string) =
  echo "Error: " + fgRed, msg

proc eval(callee, args: sink Node) =
  try:
    let (res, trace) = interpret(lang, tree(nkCall, callee, args))
    if trace.input.kind != nkFail: # guard against empty traces
      var str: ColText
      pretty(str, trace, 0)
      echo str
    prev = res
    echo "Got: " + fgGreen, prev
  except CatchableError:
    error "evaluation failed"

proc handleCmd(cmd: SexpNode) =
  ## The command processing logic.
  template check(cond: bool, shape: string) =
    if not cond:
      error "expected command of the form '$1'" % [shape]
      return

  template requireLang() =
    if langOpt.isNone:
      error "no language definition is loaded"
      return

  check cmd.kind == SList and cmd.len > 0 and cmd[0].kind == SSymbol,
        "(<cmd> ...)"

  case cmd[0].symbol
  of "quit":
    quit(0)
  of "set":
    check cmd.len == 2 and cmd[1].kind == SSymbol, "(set <var-name>)"
    # store the previously computed result in a variable with the given name
    vars[cmd[1].symbol] = prev
  of "term":
    check cmd.len == 2, "(term <term>)"
    try:
      prev = fromSexp(cmd[1])
    except ValueError as e:
      error e.msg
  of "default":
    check cmd.len == 2 and cmd[1].kind == SSymbol, "(default <type-name>)"
    requireLang()
    # compute the default value for the given type
    for typ, name in lang.names.pairs:
      if name == cmd[1].symbol:
        prev = getDefault(lang, typ)
        echo "Got: " + fgGreen, prev
        return

    error "no type with given name found"
  of "apply":
    check cmd.len >= 2 and cmd[1].kind == SSymbol, "(run <name> <arg>*)"
    requireLang()
    let callee = pick(lang, cmd[1].symbol)
    if callee.kind == nkFail:
      error "no function or relation found with the given name"
    elif cmd.len == 2:
      # pass the previous command's result
      eval(callee, prev)
    else:
      var args: Node
      try:
        args = tree(nkTuple,
          map(cmd.elems.toOpenArray(2, cmd.len - 1),
              proc(x: auto): auto = fromSexp(x)))
      except ValueError as e:
        error e.msg
        return

      if args.len == 1:
        args = args[0] # unpack single-element tuples
      eval(callee, args)
  of "import":
    check cmd.len == 2 and cmd[1].kind == SString, "(import <relative-path>)"
    let path =
      when defined(windows): getTempDir() / "queryshell_load.dll"
      else:                  getTempDir() / "queryshell_load.so"
    echo "compiling the loader..."
    # instead of via a temporary file, the loader code is passed directly on
    # the command line. This is faster and produces less artifacts
    let res = execCmd(CompileCmd % [quoteShell(path),
                                    quoteShell(LoaderCode % [cmd[1].str])])
    if res == 0:
      let lib = loadLib(path)
      if lib != nil:
        let prc = cast[proc(): ptr LangDef {.cdecl.}](lib.symAddr("load"))
        if prc != nil:
          var inst = prc()[]
          # detach the string payloads in inst (this must happen before the
          # library is unloaded, otherwise the payload pointers start to
          # dangle)
          prepareMutation(inst)
          langOpt = some(inst)
          echo "success!"
        else:
          error "library seems to be corrupt"
        unloadLib(lib)
      else:
        error "failed to load library"
    else:
      error "compiling the loader failed"
  else:
    error "expected 'quit', 'set', 'term', 'default', 'apply', or 'import'"

# the main loop:
let stream = newLineBufferedStream()
var iter = parse
while not finished(iter):
  if depth > 0:
    stdout.write "  "
    for i in 0..<depth:
      stdout.write "  "
  else:
    stdout.write "> "
  stdout.flushFile()

  var cmd: SexpNode
  # process all closed S-expressions
  while ((cmd, depth) = iter(stream); cmd != nil):
    handleCmd(cmd)
