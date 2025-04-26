## Implements some macros and types to make writing code in continuation-
## passing style easier.

import std/macros

{.experimental: "callOperator".}

type
  CellBase = ref object of RootObj
    ## Header for a heap cell.
    copy: (proc(x: CellBase): CellBase {.nimcall, raises: [].})
  Cell[T] = ref object of CellBase
    val: T

  CellRef = object
    ## Type-erased managed unique pointer to a heap cell. Needed for storing
    ## the environment for continuations.
    p: CellBase

# --- cell implementation

proc `=copy`(dst: var CellRef, src: CellRef) =
  if dst.p != src.p: # do nothing for self assignments
    if src.p.isNil:
      dst.p = nil
    else:
      dst.p = src.p.copy(src.p)

# the object checks in `take` have significant overhead, but since the
# procedure is only used internally, we know that the dynamic type is always
# correct and thus can safely disable the checks
{.push checks: off.}

proc take[T](c: sink CellRef): T {.inline.} =
  ## Returns the value from the given cell, `c`, which has to have dynamic
  ## type `T`.
  move (Cell[T])(c.p).val

{.pop.}

proc copyImpl[T](x: CellBase): CellBase =
  Cell[T](val: Cell[T](x).val, copy: x.copy)

proc newCell[T](val: sink T): CellRef {.inline.} =
  CellRef(p: Cell[T](val: val, copy: copyImpl[T]))

# ---- macro helpers

template strip[T](x: typedesc[sink T]): typedesc = T

proc paramType(): NimNode =
  newCall(ident"sink", bindSym"CellRef")

macro cont*(captures, lambda: untyped): untyped =
  ## Meant to be used as a pragma. Turns a lambda expression into a
  ## continuation construction, with all items in the `captures` list captured
  ## by value (or address).
  lambda.expectKind nnkLambda
  lambda.pragma.add ident"tailcall"

  let
    unpack = nnkVarTuple.newTree() ## the capture tuple unpacking
    typ    = nnkTupleConstr.newTree() ## the type of the capture tuple
    constr = nnkTupleConstr.newTree() ## the capture tuple construction

  # create the adapter/thunk procedure. It's responsible for unpacking the
  # environment
  let wrapper = newProc(newEmptyNode())
  wrapper.pragma = nnkPragma.newTree(ident"tailcall")
  wrapper.body = newStmtList()
  wrapper.params = lambda.params.copyNimTree()
  wrapper.params.add newIdentDefs(ident"env", paramType())

  let call = newCall(lambda) # the call to the original lambda
  for i in 1..<lambda.params.len:
    for j in 0..<lambda.params[i].len-2:
      call.add lambda.params[i][j]

  proc fixedTypeof(n: NimNode): NimNode =
    # work around the compiler not dropping the sink modifier with `typeof`
    newCall(bindSym"strip", quote do: typeof(`n`))

  captures.expectKind {nnkPar, nnkTupleConstr}
  # handle the captures:
  for it in captures.items:
    case it.kind
    of nnkPtrTy:
      # the value is captured by address. It's passed to the inner procedure as
      # an immutable parameter
      it.expectLen 1
      let name = it[0]
      unpack.add name
      call.add (quote do: `name`[])
      constr.add nnkAddr.newTree(name)
      typ.add nnkPtrTy.newTree(fixedTypeof(name))
      lambda.params.add newIdentDefs(name, quote do: typeof(`name`[]))
    of nnkIdent:
      # capture by value -- the value is passed to the inner procedure as a
      # sink parameter
      unpack.add it
      call.add it
      constr.add it
      typ.add fixedTypeof(it)
      lambda.params.add newIdentDefs(it, quote do: sink typeof(`it`))
    else:
      error("expected identifier or `ptr x`", it)

  # finish the tuple unpacking statement and emit it into the wrapper
  # procedure:
  unpack.add newEmptyNode()
  unpack.add newCall(nnkBracketExpr.newTree(bindSym"take", typ), ident"env")

  wrapper.body.add nnkVarSection.newTree(unpack)
  wrapper.body.add call

  # the original lambda expression becomes a continuation construction
  result = nnkTupleConstr.newTree(wrapper, newCall(bindSym"newCell", constr))

macro cont*(lambda: untyped): untyped =
  ## Meant to be used as a pragma. Turns a lambda expression into a
  ## continuation construction.
  lambda.expectKind nnkLambda
  lambda.params.add newIdentDefs(ident"env", paramType())
  lambda.pragma.add ident"tailcall"
  result = nnkTupleConstr.newTree(
    lambda,
    nnkObjConstr.newTree(bindSym"CellRef"))

macro contcc*(typ: untyped): typedesc =
  ## A proc type annotation, marking the proc type as being a continuation.
  ## Storage wise, a continuation is a tuple.
  typ.expectKind nnkProcTy

  let ntyp = copyNimTree(typ)
  ntyp.pragma.add ident"tailcall"
  ntyp[0].add newIdentDefs(ident"env", paramType())

  result = nnkTupleConstr.newTree(ntyp, bindSym"CellRef")

  # for reasons that are beyond silly (the compiler analyzes the proc type
  # expression twice, with each macro pragma application being destructive
  # to the original AST, but only within type sections), we need to add the
  # pragma back to the original AST...
  typ.pragma.add ident"contcc"

macro `()`*[T](c: (T, CellRef), args: varargs[untyped]): untyped =
  ## Invokes continuation `c` with the given `args`, consuming it in the
  ## process.
  let
    callee = genSym(nskLet, "callee")
    arg    = genSym(nskLet, "arg")
    call   = newCall(callee)
  for it in args.items:
    call.add it
  call.add arg

  result = quote do:
    let (`callee`, `arg`) = `c`
    `call`
