## This implements a temporary pass for translating the parse-tree of the
## source language into the currently highest-level intermediate language.
## It's there so that development of the source language can already commence
## while the the intermediate languages are still being developed.
##
## The focus is on correctness. Performance, code quality, and overall
## architecture (of this module) are of secondary concern.

import
  std/[algorithm, sequtils, tables],
  passes/[builders, ir, syntax, trees],
  phy/[reporting, tree_parser, type_rendering, types],
  vm/[utils]

from std/strutils import `%`

import passes/syntax_source except NodeKind

type
  SourceKind = syntax_source.NodeKind
  InTree     = PackedTree[SourceKind]
  Node       = TreeNode[NodeKind]
  NodeSeq    = seq[Node]

  EntityKind = enum
    ekNone        ## signals "non-existent"
    ekBuiltinVal  ## some built-in named value
    ekBuiltinProc ## some built-in procedure
    ekProc
    ekType
    ekLocal
    ekParam
    ekValue       ## a value bound to an identifier via a match pattern

  Entity = object
    kind: EntityKind
    id: int
      ## ID of the procedure or type. It's an index into the respective list

  ProcInfo* = object
    typ*: SemType
      ## the procedure's type

  Scope = Table[string, Entity]

  TypeAttachedOp = enum
    ## Type-attached operators.
    opCopy
    opAt

  ModuleCtx* = object
    ## The translation/analysis context for a single module.
    reporter: ref ReportContext[string]
    # XXX: strings being used for diagnostics is a temporary measure. Message
    #      formatting should eventually be separated from diagnostic emission

    literals: Literals
    types: Builder[NodeKind]
      ## the in-progress type section
    numTypes: int
    aliases: seq[SemType]
      ## the list of type aliases
    procs: seq[NodeSeq]
      ## all IL procedure definitions
    procList*: seq[ProcInfo]
    globals: Builder[NodeKind]
      ## the in-progress global variable section
    exports: Builder[NodeKind]
      ## the in-progress export section

    typeOps: Table[(TypeAttachedOp, SemType), uint32]
      ## caches the generated type-attached operators (i.e., procedures)

    procTypeCache: Table[SemType, uint32]
      ## caches the ID of IL signature types generated for procedure types.
      ## They're structural types in the source language, but nominal types in
      ## the target IL

    scopes: seq[Scope]
      ## the stack of scopes. The last item always represents the current scope

    entry*: int
      ## index of the module's entry procedure. -1 means that there's none

    # procedure context:
    retType: SemType
    locals: seq[SemType]
      ## all locals part of the procedure
    params: seq[tuple[typ: SemType, local: uint32]]
      ## the parameters for the procedure

  ExprFlag {.pure.} = enum
    Lvalue ## the expression is an lvalue. The flags absence implies
           ## that the expression is an rvalue or void expression
    Mutable## the expression refers to a mutable lvalue. Only makes sense
           ## when the ``Lvalue`` flag is present

  ExprType = tuple
    ## Returned by expression analysis. Carries additional attributes about
    ## the expression, not just the type.
    typ: SemType
    attribs: set[ExprFlag]

  Expr = object
    # XXX: the target IL doesn't support expression lists (yet), so we have
    #      to apply the necessary lowering here, for now. Efficiency doesn't
    #      matter
    stmts: seq[IrNode] # can be empty
    expr: IrNode
    typ: SemType
    attribs: set[ExprFlag]

const
  BuiltIns = {
    "+": ekBuiltinProc,
    "-": ekBuiltinProc,
    "*": ekBuiltinProc,
    "/": ekBuiltinProc,
    "div": ekBuiltinProc,
    "mod": ekBuiltinProc,
    "==": ekBuiltinProc,
    "<=": ekBuiltinProc,
    "<": ekBuiltinProc,
    "not": ekBuiltinProc,
    "len": ekBuiltinProc,
    "concat": ekBuiltinProc,
    "true": ekBuiltinVal,
    "false": ekBuiltinVal
  }.toTable

  UnitNode = IrNode(kind: IntVal, intVal: 0)
    ## the node representing the unitary value
  unitExpr = Expr(expr: UnitNode, typ: prim(tkUnit))
    ## the expression evaluating to the unitary value

  # the allocator and generic seq procedures currently use static IDs
  AllocProc = 0
  DeallocProc {.used.} = 1
  ReallocProc {.used.} = 2
  PrepareAddProc = 4

using
  c: var ModuleCtx
  t: InTree
  bu: var Builder[NodeKind]
  expr: var IrNode
  stmts: var seq[IrNode]

func align(val: SizeUnit, to: SizeUnit): SizeUnit =
  ## Rounds `val` to the multiple of `to`, the latter must be a power of two.
  let mask = to - 1
  (val + mask) and not mask

template `+`(t: SemType, a: set[ExprFlag]): ExprType =
  ## Convenience shortcut for creating an ``ExprType``.
  (typ: t, attribs: a)

proc error(c; message: sink string) =
  ## Sends the error diagnostic `message` to the reporter.
  c.reporter.error(message)

func lookup(c: ModuleCtx, name: string): Entity =
  ## Implements the lookup action described in the specification.
  var i = c.scopes.high
  while i >= 0:
    result = c.scopes[i].getOrDefault(name, Entity(kind: ekNone))
    if result.kind != ekNone:
      return
    dec i

  # try the builtins
  result.kind = BuiltIns.getOrDefault(name, ekNone)

func addDecl(c; name: string, entity: sink Entity) =
  ## Adds the `entity` with name `name` to the current scope, ignoring whether
  ## it already existed.
  c.scopes[^1][name] = entity

func removeDecl(c; name: string) {.used.} =
  ## Removes the entity with `name` from the current scope.
  c.scopes[^1].del(name)

func openScope(c) =
  ## Opens a new scope and makes it the current one.
  c.scopes.add default(typeof(c.scopes[0]))

func closeScope(c) =
  ## Closes the current scope and makes its parent the current one.
  c.scopes.shrink(c.scopes.len - 1)

template buildTree(kind: NodeKind, body: untyped): seq[Node] =
  ## Injects a builder named `bu` into the scope of `body` and returns
  ## the builder's nodes after evaluating `body`.
  if true:
    var bu {.inject.} = initBuilder(kind)
    body
    finish(bu)
  else:
    unreachable()

template addType(c; kind: NodeKind, body: untyped): uint32 =
  c.types.subTree kind:
    body
  (let r = c.numTypes; inc c.numTypes; r.uint32)

proc addType(c; node: Node): uint32 =
  c.types.add node
  result = c.numTypes.uint32
  inc c.numTypes

proc expect(c; name: string, ent: Entity, kind: EntityKind): bool =
  ## Convenience procedure for reporting an error if `ent` is not of the given
  ## `kind`. Returns 'true' if it is.
  if ent.kind == kind:
    true
  elif ent.kind == ekNone:
    c.error("undeclared identifier: '" & name & "'")
    false
  else:
    c.error("'" & name & "' is not a " & $kind & " name")
    false

proc expectNot(c; typ: sink SemType, kind: TypeKind): SemType =
  ## If `typ` has the given `kind`, reports an error and returns the error
  ## type. Otherwise returns `typ` as-is.
  if typ.kind != kind:
    result = typ
  else:
    c.error("type not allowed in this context")
    result = errorType()

proc unionOf(types: openArray[SemType]): tuple[typ: SemType, folded: bool] =
  ## Attempts to create a union type from `types`. If the resulting union would
  ## only consist of a single type, the single type is returned and `folded` is
  ## set to true.
  if types.len == 1:
    (types[0], true)
  else:
    var union = SemType(kind: tkUnion)
    for it in types.items:
      let at = lowerBound(union.elems, it, cmp)
      if at >= union.elems.len or union.elems[at] != it:
        union.elems.insert(it, at)

    if union.elems.len == 1:
      (union.elems[0], true)
    else:
      (union, false)

proc evalType(c; t; n: NodeIndex): SemType =
  ## Evaluates a type expression, yielding the resulting type.
  case t[n].kind
  of VoidTy:  prim(tkVoid)
  of UnitTy:  prim(tkUnit)
  of BoolTy:  prim(tkBool)
  of CharTy:  prim(tkChar)
  of IntTy:   prim(tkInt)
  of FloatTy: prim(tkFloat)
  of SourceKind.ArrayTy:
    let length = t.getInt(t.child(n, 0))
    let typ = c.expectNot(c.evalType(t, t.child(n, 1)), tkVoid)
    if length < 0:
      c.error("array length must not be negative")
      errorType()
    elif length > high(uint32).int:
      c.error("arrays must not have more than 2^32 elements")
      errorType()
    else:
      arrayType(SizeUnit(length), typ)
  of TupleTy:
    if t.len(n) == 0:
      prim(tkUnit)
    else:
      var tup = SemType(kind: tkTuple)
      for it in t.items(n):
        var elem = evalType(c, t, it)
        if elem.kind == tkVoid:
          c.error("'void' type cannot be part of tuple type")
          elem = errorType()
        tup.elems.add elem
      tup
  of RecordTy:
    var rec = SemType(kind: tkRecord)
    for it in t.items(n):
      let
        name = t.getString(t.child(it, 0))
        elem = c.expectNot(evalType(c, t, t.child(it, 1)), tkVoid)
        i = lowerBound(rec.fields, name,
          proc(a, b: auto): int = cmp(a.name, b))
      # important: keep the lexicographic order of the fields intact
      if i >= rec.fields.len or rec.fields[i].name != name:
        rec.fields.insert((name, elem), i)
      else:
        c.error("record type has a field with name '$1'" % [name])
    rec
  of UnionTy:
    var list = newSeq[SemType]()
    for i, it in t.pairs(n):
      # make sure to add the types in a sorted fashion, so that
      # ``union(int, float)`` and ``union(float, int)`` result in the same type
      let
        typ = c.expectNot(c.evalType(t, it), tkVoid)
        at = lowerBound(list, typ, cmp)

      if at < list.len and list[at] == typ:
        if typ.kind != tkError:
          c.error("union type operands must be unique")
      else:
        list.add typ

    SemType(kind: tkUnion, elems: list)
  of SourceKind.ProcTy:
    # anything goes as the return type
    var list = @[c.evalType(t, t.child(n, 0))]

    for it in t.items(n, 1):
      list.add c.expectNot(c.evalType(t, it), tkVoid)

    SemType(kind: tkProc, elems: list)
  of SourceKind.SeqTy:
    SemType(kind: tkSeq,
            elems: @[c.expectNot(c.evalType(t, t.child(n, 0)), tkVoid)])
  of Ident:
    let
      name = t.getString(n)
      ent  = c.lookup(name)
    if c.expect(name, ent, ekType):
      c.aliases[ent.id]
    else:
      errorType()
  else:       unreachable() # syntax error

proc typeToIL(c; typ: SemType): uint32 =
  case typ.kind
  of tkVoid:
    unreachable()
  of tkUnit:
    # XXX: there's no unit type in the target IL, and in order to not having
    #      to rewrite all ``unit`` type usages here, we're translating the
    #      type to a 1-byte integer
    c.addType Node(kind: Int, val: 1)
  of tkBool:
    c.addType Node(kind: Int, val: 1)
  of tkChar:
    c.addType Node(kind: UInt, val: 1)
  of tkInt, tkError:
    c.addType Node(kind: Int, val: 8)
  of tkFloat:
    c.addType Node(kind: Float, val: 8)
  of tkPointer:
    c.addType Node(kind: Ptr)
  of tkArray:
    let elem = c.typeToIL(typ.elem[0])
    c.addType Array:
      c.types.add Node(kind: Immediate, val: paddedSize(typ).uint32)
      c.types.add Node(kind: Immediate, val: alignment(typ).uint32)
      c.types.add Node(kind: Immediate, val: uint32(typ.length)) # length
      c.types.add Node(kind: Type, val: elem)
  of tkTuple:
    let args = mapIt(typ.elems, c.typeToIL(it))
    c.addType Record:
      c.types.add Node(kind: Immediate, val: paddedSize(typ).uint32)
      c.types.add Node(kind: Immediate, val: alignment(typ).uint32)
      var off = 0 ## the current field offset
      for i, it in args.pairs:
        off = align(off, alignment(typ.elems[i]))
        c.types.subTree Field:
          c.types.add Node(kind: Immediate, val: off.uint32)
          c.types.add Node(kind: Type, val: it)
        off += paddedSize(typ.elems[i])
  of tkRecord:
    # records and tuples share the same translation logic
    c.typeToIL(SemType(kind: tkTuple, elems: mapIt(typ.fields, it.typ)))
  of tkUnion:
    let args = mapIt(typ.elems, c.typeToIL(it))
    let inner = c.addType Union:
      c.types.add Node(kind: Immediate, val: innerSize(typ).uint32)
      c.types.add Node(kind: Immediate, val: innerAlignment(typ).uint32)
      for it in args.items:
        c.types.add Node(kind: Type, val: it)

    let tag = c.typeToIL(prim(tkInt))
    c.addType Record:
      c.types.add Node(kind: Immediate, val: paddedSize(typ).uint32)
      c.types.add Node(kind: Immediate, val: alignment(typ).uint32)
      # the tag field:
      c.types.subTree Field:
        c.types.add Node(kind: Immediate, val: 0)
        c.types.add Node(kind: Type, val: tag)
      # the actual union:
      c.types.subTree Field:
        c.types.add Node(kind: Immediate, val: 8)
        c.types.add Node(kind: Type, val: inner)
  of tkProc:
    # a proc type is used to represent both procedure signatures and the type
    # of procedural values. For values, the underlying storage type
    # is a pointer
    c.addType Node(kind: Ptr)
  of tkSeq:
    let
      lengthType  = c.typeToIL(prim(tkInt))
    c.addType Record:
      c.types.add Node(kind: Immediate, val: paddedSize(typ).uint32)
      c.types.add Node(kind: Immediate, val: alignment(typ).uint32)
      # the length field:
      c.types.subTree Field:
        c.types.add Node(kind: Immediate, val: 0)
        c.types.add Node(kind: Type, val: lengthType)
      # the payload field:
      c.types.subTree Field:
        c.types.add Node(kind: Immediate, val: 8)
        c.types.add Node(kind: Ptr)

func numILParams(typ: SemType): int =
  ## Returns the number of parameters the IL signature type generated from
  ## `typ` is going to have.
  assert typ.kind == tkProc
  typ.elems.len - 1

proc rawGenProcType(c; typ: SemType): uint32 =
  ## Generates the IL representation for the procedure signature type `typ`
  ## and adds it to `c`.
  assert typ.kind == tkProc
  let params = mapIt(typ.elems.toOpenArray(1, typ.elems.high)):
    c.typeToIL(it)

  template addParams() =
    for p in params.items:
      c.types.add Node(kind: Type, val: p)

  case typ.elems[0].kind
  of tkVoid:
    c.addType ProcTy:
      c.types.subTree Void: discard
      addParams()
  else:
    let typId = c.typeToIL(typ.elems[0])
    c.addType ProcTy:
      c.types.add Node(kind: Type, val: typId)
      addParams()

proc genProcType(c; typ: SemType): uint32 =
  ## Generates and caches the IL representation for the procedure signature
  ## type `typ`, or returns the cached ID if it already exists.
  c.procTypeCache.withValue typ, val:
    result = val[]
  do:
    result = rawGenProcType(c, typ)
    c.procTypeCache[typ] = result

proc payloadAlignment(typ: SemType): SizeUnit =
  ## Computes the alignment for a seq payload for type `typ`.
  max(alignment(prim(tkInt)), alignment(typ))

proc genPayloadType(c; typ: SemType): uint32 =
  ## Generates and emits the payload type for a sequence with the given
  ## element type (`typ`). Returns the ID of the payload type.
  # TODO: cache the type description, so that it's only emitted once per
  #       element type
  let
    intType = c.typeToIL(prim(tkInt))
    elem = c.typeToIL(typ)

  let arrayType = c.addType Array:
    c.types.add Node(kind: Immediate, val: 1) # size
    c.types.add Node(kind: Immediate, val: alignment(typ).uint32) # alignment
    c.types.add Node(kind: Immediate, val: 0)
    c.types.add Node(kind: Type, val: elem)

  c.addType Record:
    c.types.add Node(kind: Immediate, val: 9)
    c.types.add Node(kind: Immediate, val: payloadAlignment(typ).uint32)
    # the capacity field:
    c.types.subTree Field:
      c.types.add Node(kind: Immediate, val: 0)
      c.types.add Node(kind: Type, val: intType)
    # the data field:
    c.types.subTree Field:
      c.types.add Node(kind: Immediate, val: 8)
      c.types.add Node(kind: Type, val: arrayType)

proc addProc(c; typ: sink SemType, def: seq[Node]): int =
  ## Adds a procedure with signature `typ` and definition `def` to the
  ## context, returning the ID to address it with.
  c.procs.add def
  c.procList.add ProcInfo(typ: typ)
  result = c.procList.high

proc getTypeBoundOp(c; op: TypeAttachedOp, typ: SemType): uint32

proc genPayloadAccess(c; e: sink IrNode, typ: SemType): IrNode =
  assert typ.kind == tkSeq
  newDeref(c.genPayloadType(typ.elems[0]), newFieldExpr(e, 1))

proc genSeqAccess(c; e, idx: sink IrNode, typ: SemType): IrNode =
  newAt(newFieldExpr(c.genPayloadAccess(e, typ), 1), idx)

proc genCapAccess(c; e: sink IrNode, typ: SemType): IrNode =
  newFieldExpr(c.genPayloadAccess(e, typ), 0)

proc newIntOp(c; op: NodeKind, a, b: sink IrNode): IrNode =
  newBinaryOp(op, c.typeToIL(prim(tkInt)), a, b)

proc newCmpOp(c; op: NodeKind, a, b: sink IrNode): IrNode =
  newBinaryOp(op, c.typeToIL(prim(tkBool)), a, b)

proc newAllocCall(size, align: sink IrNode): IrNode =
  newCall(AllocProc, @[size, align])

proc genTypeBoundOp(c; op: TypeAttachedOp, typ: SemType): uint32 =
  ## Synthesizes and emits the `op` type-bound operator for `typ`. Returns the
  ## ID of the synthesized procedure; no caching is performed.
  var
    procTy: SemType
    params: seq[uint32]
    locals: seq[SemType]
    body: IrNode

  case op
  of opCopy:
    # copy(x: T) -> T
    procTy = SemType(kind: tkProc, elems: @[typ, typ])
    params.add 0
    locals.add typ # parameter
    locals.add typ # result
    let
      src = newLocal(0)
      dst = newLocal(1)

    case typ.kind
    of tkSeq:
      let
        srcLen = newFieldExpr(src, 0)
        dstLen = newFieldExpr(dst, 0)

      var then = IrNode(kind: Stmts)
      then.add newAsgn(dstLen, newIntVal(0))
      then.add newAsgn(newFieldExpr(dst, 1), newIntVal(0))
      then.add newReturn(dst)

      var els = IrNode(kind: Stmts)
      els.add newAsgn(dstLen, srcLen)
      # the size of the payload is:
      #   align(sizeof(capacity), alignment(element)) + sizeof(element) * length
      els.add newAsgn(newFieldExpr(dst, 1), newAllocCall(
        c.newIntOp(Add,
          c.newIntOp(Mul,
            srcLen,
            newIntVal(paddedSize(typ.elems[0]))),
          newIntVal(align(size(prim(tkInt)), alignment(typ.elems[0])))),
        newIntVal(alignment(typ.elems[0]))))

      els.add newAsgn(c.genCapAccess(dst, typ), srcLen)

      # set up the loop counter:
      let counter = newLocal(2)
      locals.add prim(tkInt)
      els.add newAsgn(counter, newIntVal(0))

      var loopBody = IrNode(kind: Stmts)
      loopBody.add newIf(c.newIntOp(Eq, counter, srcLen), newBreak(1))

      let
        srcElem = c.genSeqAccess(src, counter, typ)
        dstElem = c.genSeqAccess(dst, counter, typ)

      if isTriviallyCopyable(typ.elems[0]):
        # XXX: using a memcopy to copy all elements at once would most likely
        #      be faster
        loopBody.add newAsgn(dstElem, srcElem)
      else:
        loopBody.add newAsgn(dstElem,
          newCall(c.getTypeBoundOp(opCopy, typ.elems[0]), srcElem))

      loopBody.add newAsgn(counter, c.newIntOp(Add, counter, newIntVal(1)))

      els.add IrNode(kind: Loop, children: @[loopBody])
      els.add newReturn(dst)
      body = newIf(c.newIntOp(Eq, srcLen, newIntVal(0)), then, els)
    of tkArray:
      # set up the loop counter:
      let counter = newLocal(2)
      locals.add prim(tkInt)
      body.add newAsgn(counter, newIntVal(0))

      var loopBody = IrNode(kind: Stmts)
      loopBody.add newIf(c.newIntOp(Eq, counter, newIntVal(typ.length)),
                         newBreak(1))
      loopBody.add newAsgn(newAt(dst, counter),
        newCall(c.getTypeBoundOp(opCopy, typ.elems[0]), newAt(src, counter)))
      loopBody.add newAsgn(counter, c.newIntOp(Add, counter, newIntVal(1)))

      body.add IrNode(kind: Loop, children: @[loopBody])
      body.add newReturn(dst)
    of tkTuple:
      body = IrNode(kind: Stmts)
      # copy each tuple element from the source to the destination:
      for i, it in typ.elems.pairs:
        if isTriviallyCopyable(it):
          body.add newAsgn(newFieldExpr(dst, i),
            newFieldExpr(src, i))
        else:
          body.add newAsgn(newFieldExpr(dst, i),
            newCall(c.getTypeBoundOp(opCopy, it), newFieldExpr(src, i)))

      body.add newReturn(dst)
    of tkRecord:
      body = IrNode(kind: Stmts)
      for i, it in typ.fields.pairs:
        if isTriviallyCopyable(it.typ):
          body.add newAsgn(newFieldExpr(dst, i),
            newFieldExpr(src, i))
        else:
          body.add newAsgn(newFieldExpr(dst, i),
            newCall(c.getTypeBoundOp(opCopy, it.typ), newFieldExpr(src, i)))

      body.add newReturn(dst)
    of tkUnion:
      body = IrNode(kind: Stmts)
      # copy the tag:
      body.add newAsgn(newFieldExpr(dst, 0), newFieldExpr(src, 0))
      # copy the value:
      locals.add prim(tkInt)
      # case statements in the target IL don't allow a field access as the
      # selector, so an intermediate temporary is needed
      body.add newAsgn(newLocal(2), newFieldExpr(dst, 0))
      var caseStmt = newCase(c.typeToIL(prim(tkInt)), newLocal(2))
      for i, it in typ.elems.pairs:
        var val = newFieldExpr(newFieldExpr(src, 1), i)
        if not isTriviallyCopyable(it):
          val = newCall(c.getTypeBoundOp(opCopy, it), val)
        caseStmt.add newChoice(newIntVal(i),
          newAsgn(newFieldExpr(newFieldExpr(dst, 1), i), val))

      body.add caseStmt
      body.add newReturn(dst)
    of AllTypes - AggregateTypes:
      unreachable() # no copy procedure needed
  of opAt:
    case typ.kind
    of tkSeq:
      # at(s: seq(T), index: int) -> pointer
      procTy = SemType(kind: tkProc,
                       elems: @[prim(tkPointer), typ, prim(tkInt)])
      params.add 0
      params.add 1
      locals.add typ
      locals.add prim(tkInt)

      let
        s   = newLocal(0)
        idx = newLocal(1)

      body = IrNode(kind: Stmts)
      body.add newIf(
        c.newIntOp(Le, newIntVal(0), idx),
        newIf(
          c.newIntOp(Lt, idx, newFieldExpr(s, 0)),
          newReturn(newAddr(c.genSeqAccess(s, idx, typ)))))
      body.add newUnreachable()
    of tkArray:
      # at(arr: pointer, index: int) -> pointer
      procTy = SemType(kind: tkProc,
                       elems: @[prim(tkPointer), prim(tkPointer), prim(tkInt)])
      params.add 0
      params.add 1
      locals.add prim(tkPointer)
      locals.add prim(tkInt)

      let
        arr = newLocal(0)
        idx = newLocal(1)

      body = IrNode(kind: Stmts)
      body.add newIf(
        c.newIntOp(Le, newIntVal(0), idx),
        newIf(
          c.newIntOp(Lt, idx, newIntVal(typ.length)),
          newReturn(newAddr(newAt(newDeref(c.typeToIL(typ), arr), idx)))))
      body.add newUnreachable()
    of tkTuple:
      # at(s: tuple, index: int, tmp: pointer) -> pointer
      let (ret, folded) = unionOf(typ.elems)
      procTy = SemType(kind: tkProc,
                       elems: @[prim(tkPointer), typ, prim(tkInt),
                                prim(tkPointer)])
      params.add 0
      params.add 1
      params.add 2
      locals.add typ
      locals.add prim(tkInt)
      locals.add prim(tkPointer)
      locals.add prim(tkBool) # temporary
      let
        tup = newLocal(0)
        idx = newLocal(1)
        res = newDeref(c.typeToIL(ret), newLocal(2))

      # the extra pointer parameters must hold a pointer to a location that is
      # used as an intermediary. The external intermediary is needed so that
      # the procedure can return a pointer to the result value, which is needed
      # for the receiver to wrap it in an Deref, so that the tuple access can
      # be an lvalue expression in the IL...

      body = IrNode(kind: Stmts)
      var caseStmt = newCase(c.typeToIL(prim(tkInt)), idx)
      for i, it in typ.elems.pairs:
        var list = IrNode(kind: Stmts)
        if folded:
          # the tuple is really an array
          list.add newAsgn(res, newFieldExpr(tup, i))
        else:
          let pos = find(typ.elems, it)
          list.add newAsgn(newFieldExpr(res, 0), newIntVal(pos))
          list.add newAsgn(newFieldExpr(newFieldExpr(res, 1), pos),
                           newFieldExpr(tup, i))
        caseStmt.add newChoice(newIntVal(i), list)

      let cond = newLocal(3)
      body.add newIf(c.newCmpOp(Le, newIntVal(0), idx),
        newAsgn(cond, c.newCmpOp(Lt, idx, newIntVal(typ.elems.len))),
        newAsgn(cond, newIntVal(0)))
      body.add newIf(cond, caseStmt, newUnreachable())
      body.add newReturn(newLocal(2))
    else:
      unreachable()

  # assemble the final definition and add it to the module:
  var bu = initBuilder(ProcDef)
  bu.add Node(kind: Type, val: c.genProcType(procTy))
  bu.subTree Params:
    for it in params.items:
      bu.add Node(kind: Local, val: it)
  bu.subTree Locals:
    for it in locals.items:
      bu.add Node(kind: Type, val: c.typeToIL(it))
  convert(body, c.literals, bu)
  result = c.addProc(procTy, finish(bu)).uint32

proc getTypeBoundOp(c; op: TypeAttachedOp, typ: SemType): uint32 =
  ## Returns the cached type-bound operator `op` for `typ`, or creates and
  ## caches it first.
  c.typeOps.withValue (op, typ), val:
    result = val[]
  do:
    result = c.genTypeBoundOp(op, typ)
    c.typeOps[(op, typ)] = result

proc resetProcContext(c) =
  c.locals.setLen(0) # re-use the memory

proc newTemp(c; typ: SemType): IrNode =
  ## Allocates a new temporary of `typ` type.
  case typ.kind
  of tkVoid:
    # do not create a temp for void
    result = IrNode(kind: None)
  else:
    result = newLocal(c.locals.len.uint32)
    c.locals.add typ

proc use(c; e: sink Expr; stmts): IrNode =
  ## Adds `e`'s statements to `stmts` and returns the usage-context specific
  ## version of the expression.
  stmts.add e.stmts
  if Lvalue in e.attribs and not isTriviallyCopyable(e.typ):
    newCall(c.getTypeBoundOp(opCopy, e.typ), e.expr)
  else:
    e.expr

proc wrap(c; e: sink Expr, dest: IrNode): IrNode =
  ## Turns `e` into a statement list. The expression part is turned into an
  ## assignment to `dest`, but only if not a void expression.
  result = IrNode(kind: Stmts)
  if e.typ.kind == tkVoid:
    result.children = e.stmts
  else:
    result.add newAsgn(dest, use(c, e, result.children))

proc inline(e: sink Expr, stmts): IrNode =
  ## Adds the statement part of `e` to `stmts` and returns the expression part.
  stmts.add e.stmts
  e.expr

proc capture(c; e: sink Expr; stmts): IrNode =
  ## Commits expression `e` to a fresh temporary. This is part of the
  ## expression-list lowering machinery.
  result = c.newTemp(e.typ)
  stmts.add newAsgn(result, use(c, e, stmts))

proc inlineLvalue(c; e: sink Expr; stmts): IrNode =
  ## Returns `e` as an l-value IL expression, committing `e` to a temporary
  ## first if needed.
  case e.expr.kind
  of Local, At, Field, Deref:
    stmts.add e.stmts
    result = e.expr
  else:
    # IL r-value expressions cannot be used where an l-value expression is
    # expected; going through a temporary solves this
    result = c.capture(e, stmts)

proc fitExpr(c; e: sink Expr, target: SemType): Expr =
  ## Makes sure `e` fits into the `target` type, returning the expression
  ## with the appropriate conversion operation applied. If the type of `e`
  ## is not the same as or a subtype of `target`, an error is reported.
  if e.typ == target:
    result = e
  elif e.typ.isSubtypeOf(target):
    if e.typ.kind == tkVoid:
      result = e
    else:
      result = Expr(stmts: move e.stmts, typ: target)
      # the destructive move of `e.stmts` is deliberate
      case target.kind
      of tkUnion:
        # construct a union
        let
          tmp = c.newTemp(target)
          idx = find(target.elems, e.typ)

        # ignore the type not being found in the union. This indicates that an
        # error occurred during union construction

        # emit the tag assignment:
        result.stmts.add:
          newAsgn(newFieldExpr(tmp, 0), newIntVal(idx))
        # emit the value assignment:
        result.stmts.add:
          newAsgn(newFieldExpr(newFieldExpr(tmp, 1), idx),
                  use(c, e, result.stmts))

        result.expr = tmp
      of tkError:
        # error correction: keep the original expression as is when fitting
        # to the error type
        result.typ = e.typ
        result.expr = e.expr
      else:
        unreachable()
  else:
    # TODO: this needs a better error message
    c.error("type mismatch")
    # still return a proper expression so that analysis can carry on
    if target.kind == tkVoid:
      result = Expr(typ: target, stmts: e.stmts)
    else:
      result = Expr(typ: target, stmts: e.stmts, expr: e.expr)

proc fitExprStrict(c; e: sink Expr, typ: SemType): Expr =
  ## Makes sure expression `e` fits `typ` exactly, reporting an error and
  ## returning an error-expression if not.
  if e.typ == typ:
    result = e # all good
  else:
    c.error("expected expression of type $1 but got type $2" %
            [$typ, $e.typ])
    # turn into an error expression:
    result = Expr(stmts: e.stmts, typ: errorType())

proc exprToIL(c; t: InTree, n: NodeIndex, expr, stmts): ExprType

proc openExprToIL(c; t: InTree, n: NodeIndex): Expr =
  ## Analyzes the given expression and generates the IL code for it. Symbols
  ## introduced by the analysis *escape* into the enclosing scope, hence the
  ## procedure's name.
  result.expr = IrNode(kind: None)
  (result.typ, result.attribs) = exprToIL(c, t, n, result.expr, result.stmts)
  # verify some postconditions:
  assert result.typ.kind != tkVoid or result.expr.kind == None,
         "void `Expr` cannot have a trailing expression"
  assert result.typ.kind in {tkVoid, tkError} or result.expr.kind != None,
         "non-void `Expr` must have a trailing expression"

proc exprToIL(c; t; n: NodeIndex): Expr =
  ## Analyzes the given expression and generates the IL for it. Analysis
  ## happens within a new scope, which is discarded afterwards.
  c.openScope()
  result = c.openExprToIL(t, n)
  c.closeScope()

template lenCheck(t; n: NodeIndex, expected: int) =
  ## Exits the current analysis procedure with an error, if `n` doesn't have
  ## `expected` children.
  if t.len(n) != expected:
    c.error("expected " & $expected & " arguments, but got " & $t.len(n))
    return errorType()

proc binaryArithToIL(c; t; n: NodeIndex, name: string, expr, stmts): SemType =
  ## Analyzes and emits the IL for a binary arithmetic operation.
  lenCheck(t, n, 3)

  let
    (_, a, b)  = t.triplet(n)
    eA = exprToIL(c, t, a)
    eB = exprToIL(c, t, b)

  if tkError in {eA.typ.kind, eB.typ.kind}:
    result = errorType()
  elif eA.typ != eB.typ:
    c.error("arguments have mismatching types")
    result = errorType()
  else:
    template wantType(s: set[TypeKind], msg: string) =
      if eA.typ.kind notin s:
        c.error(msg)
        return errorType()

    proc check(c; op: NodeKind, a, b: sink IrNode, stmts): IrNode {.nimcall.} =
      ## Emits a checked arithmetic operation and returns the local storing the
      ## result.
      let flag = c.newTemp(prim(tkBool))
      result = c.newTemp(prim(tkInt))
      stmts.add newAsgn(result,
        newCheckedOp(op, c.typeToIL(prim(tkInt)), a, b, flag))
      # abort execution if an overflow occurrs
      stmts.add newIf(
        newBinaryOp(Eq, c.typeToIL(prim(tkBool)), flag, newIntVal(1)),
        newUnreachable())

    result = eA.typ # later turned into an error type if wrong
    let
      valA = c.capture(eA, stmts)
      valB = c.capture(eB, stmts)
    case name
    of "+":
      case result.kind
      of tkInt:
        expr = check(c, AddChck, valA, valB, stmts)
      of tkFloat:
        expr = newBinaryOp(Add, c.typeToIL(result), valA, valB)
      else:
        c.error("arguments must be of 'int' or 'float' type")
        result = errorType()
    of "-":
      case result.kind
      of tkInt:
        expr = check(c, SubChck, valA, valB, stmts)
      of tkFloat:
        expr = newBinaryOp(Sub, c.typeToIL(result), valA, valB)
      else:
        c.error("arguments must be of 'int' or 'float' type")
        result = errorType()
    of "*":
      case result.kind
      of tkInt:
        expr = check(c, MulChck, valA, valB, stmts)
      of tkFloat:
        expr = newBinaryOp(Mul, c.typeToIL(result), valA, valB)
      else:
        c.error("arguments must be of 'int' or 'float' type")
        result = errorType()
    of "/":
      wantType {tkFloat}, "arguments must of type 'float'"
      expr = newBinaryOp(Div, c.typeToIL(result), valA, valB)
    of "div":
      wantType {tkInt}, "arguments must be of 'int' type"
      # emit a division-by-zero guard:
      stmts.add newIf(
        newBinaryOp(Eq, c.typeToIL(eA.typ), valB, newIntVal(0)),
        newUnreachable())
      # emit an overflow guard:
      stmts.add newIf(
        newBinaryOp(Eq, c.typeToIL(eA.typ), valA, newIntVal(low(int64))),
        newIf(newBinaryOp(Eq, c.typeToIL(eA.typ), valB, newIntVal(-1)),
          newUnreachable()))
      expr = newBinaryOp(Div, c.typeToIL(eA.typ), valA, valB)
    of "mod":
      wantType {tkInt}, "arguments must be of 'int' type"
      # emit a division-by-zero guard:
      stmts.add newIf(
        newBinaryOp(Eq, c.typeToIL(eA.typ), valB, newIntVal(0)),
        newUnreachable())
      expr = newBinaryOp(Mod, c.typeToIL(eA.typ), valA, valB)
    else:
      unreachable()

proc relToIL(c; t; n: NodeIndex, name: string, expr; stmts): SemType =
  ## Analyzes and emits the IL for a relational operation.
  lenCheck(t, n, 3)

  let
    (_, a, b)  = t.triplet(n)
    eA = exprToIL(c, t, a)
    eB = exprToIL(c, t, b)

  let (op, valid) =
    case name
    of "==": (Eq, {tkBool, tkInt, tkFloat})
    of "<":  (Lt, {tkInt, tkFloat})
    of "<=": (Le, {tkInt, tkFloat})
    else:   unreachable()

  if eA.typ == eB.typ and eA.typ.kind in valid:
    expr = newBinaryOp(op, c.typeToIL(eA.typ),
                       c.capture(eA, stmts),
                       c.capture(eB, stmts))
    result = prim(tkBool)
  elif tkError in {eA.typ.kind, eB.typ.kind}:
    result = errorType()
  else:
    c.error("arguments have mismatching types")
    result = errorType()

proc notToIL(c; t; n: NodeIndex, expr; stmts): SemType =
  lenCheck(t, n, 2)

  let arg = exprToIL(c, t, t.child(n, 1))

  if arg.typ.kind == tkBool:
    # a single argument, so no capture is necessary
    expr = newNot(use(c, arg, stmts))
    result = prim(tkBool)
  else:
    c.error("expected 'bool' expression")
    result = errorType()

proc userCallToIL(c; t; n: NodeIndex, expr; stmts): SemType =
  ## Analyzes a non-built-in call expression and translates it to its IL
  ## representation.
  let callee = c.exprToIL(t, t.child(n, 0))

  if callee.typ.kind == tkProc:
    proc addArgs(call: var IrNode, c; t; n: NodeIndex; prc: SemType; stmts
                ) {.nimcall.} =
      var i = 1 # 1 means argument 0
      for it in t.items(n, 1):
        # only try fitting the argument if there's a corresponding parameter
        let arg =
          if i < prc.elems.len:
            c.fitExprStrict(c.exprToIL(t, it), prc.elems[i])
          else:
            c.exprToIL(t, it)

        # capture the value to ensure a correct evaluation order between the
        # argument expressions
        let tmp = c.capture(arg, stmts)
        call.add tmp

        inc i

      if i != prc.elems.len:
        # arity mismatch
        c.error("expected $1 arguments but got $2" %
                [$(prc.elems.len - 1), $(i - 1)])

    stmts.add callee.stmts

    var call = IrNode(kind: Call)
    if callee.expr.kind == Proc:
      # the callee is a statically-known procedure; it's a static call
      call.add callee.expr
    else:
      call.add IrNode(kind: Type, id: c.genProcType(callee.typ))
      call.add callee.expr

    call.addArgs(c, t, n, callee.typ, stmts)

    # some return types need special handling
    case callee.typ.elems[0].kind
    of tkVoid:
      stmts.add call
      # mark the non-exceptional call exit as unreachable:
      stmts.add newUnreachable()
    else:
      expr = call

    result = callee.typ.elems[0]
  else:
    if callee.typ.kind != tkError: # don't cascade errors
      c.error("callee expression must be of procedural type")

    # analyze all arguments for errors and context side-effects
    for it in t.items(n, 1):
      discard c.exprToIL(t, it)

    # return an error
    result = errorType()

proc callToIL(c; t; n: NodeIndex, expr; stmts): SemType =
  # first check whether its call to a built-in procedure (those take
  # precedence)
  let callee = t.child(n, 0)
  if t[callee].kind == Ident:
    let
      name = t.getString(callee)
      ent  = c.lookup(name)

    if ent.kind == ekBuiltinProc:
      case name
      of "+", "-", "*", "/", "div", "mod":
        result = binaryArithToIL(c, t, n, name, expr, stmts)
      of "==", "<", "<=":
        result = relToIL(c, t, n, name, expr, stmts)
      of "not":
        result = notToIL(c, t, n, expr, stmts)
      of "len":
        lenCheck(t, n, 2)
        let e = c.exprToIL(t, t.child(n, 1))
        if e.typ.kind != tkSeq:
          c.error("'len' operand must be of sequence type")
        expr = newFieldExpr(inlineLvalue(c, e, stmts), 0)
        result = prim(tkInt)
      of "concat":
        lenCheck(t, n, 3)
        let s    = c.exprToIL(t, t.child(n, 1))
        var elem = c.exprToIL(t, t.child(n, 2))
        if s.typ.kind != tkSeq:
          c.error("'concat' expects sequence operand")
        else:
          # fit to the element type
          elem = c.fitExpr(elem, s.typ.elems[0])

        if elem.typ.kind == tkVoid:
          c.error("void expression is not allowed in this context")
          elem.typ = errorType()

        # duplicate the sequence and then append the element to the duplicate.
        # This is inefficient, of course, but it's also simple
        let tmp = c.newTemp(s.typ)
        stmts.add newAsgn(tmp, use(c, s, stmts))
        stmts.add newAsgn(
          newDeref(c.typeToIL(elem.typ),
            newCall(PrepareAddProc, @[newAddr(newFieldExpr(tmp, 0)),
                                      newAddr(newFieldExpr(tmp, 1)),
                                      newIntVal(paddedSize(elem.typ)),
                                      newIntVal(alignment(elem.typ))])),
          use(c, elem, stmts))

        expr = tmp
        result = s.typ
      else:
        unreachable()
      return

  # it must be a call to a user-defined procedure (or an error)
  result = userCallToIL(c, t, n, expr, stmts)

proc localDeclToIL(c; t; n: NodeIndex, stmts) =
  ## Translates a procedure-local declaration to the target IL.
  let
    (npos, init) = t.pair(n)
    name = t.getString(npos)

  var e = c.exprToIL(t, init)
  if e.typ.kind == tkVoid:
    c.error("cannot initialize local with `void` expression")
    # turn into an error expression:
    e.typ = errorType()
    e.expr = IrNode(kind: None)

  let local = c.newTemp(e.typ)
  stmts.add newAsgn(local, use(c, e, stmts))

  # verify that the name isn't in use already *after* analyzing the
  # initializer; the expression could introduce an entity with the same name
  if c.lookup(name).kind != ekNone:
    c.error("redeclaration of " & name)
    # don't abort; override the existing entity for the sake of error
    # correction

  # register the declaration *after* analyzing the expression
  c.addDecl(name, Entity(kind: ekLocal, id: local.id.int))

proc exprToIL(c; t: InTree, n: NodeIndex, expr, stmts): ExprType =
  case t[n].kind
  of SourceKind.IntVal:
    expr = newIntVal(t.getInt(n))
    result = prim(tkInt) + {}
  of SourceKind.FloatVal:
    expr = newFloatVal(t.getFloat(n))
    result = prim(tkFloat) + {}
  of SourceKind.Ident:
    let
      name = t.getString(n)
      ent = c.lookup(name)
    case ent.kind
    of ekBuiltinVal:
      case name
      of "false":
        expr = newIntVal(0)
        result = prim(tkBool) + {}
      of "true":
        expr = newIntVal(1)
        result = prim(tkBool) + {}
    of ekLocal:
      expr = newLocal(ent.id.uint32)
      result = c.locals[ent.id] + {Lvalue, Mutable}
    of ekParam:
      expr = newLocal(c.params[ent.id].local)
      result = c.params[ent.id].typ + {Lvalue}
    of ekValue:
      expr = newLocal(ent.id.uint32)
      result = c.locals[ent.id] + {}
    of ekProc:
      # expand to a procedure address (`ProcVal`), which is always correct;
      # the callsite can turn it into a static reference (`Proc`) as needed
      expr = IrNode(kind: Proc, id: ent.id.uint32)
      result = c.procList[ent.id].typ + {}
    of ekNone:
      c.error("undeclared identifier: " & t.getString(n))
      result = prim(tkError) + {}
    else:
      c.error("'" & name & "' cannot be used in this context")
      result = prim(tkError) + {}
  of SourceKind.And, SourceKind.Or:
    let
      (a, b) = t.pair(n)
      ea  = c.fitExprStrict(c.openExprToIL(t, a), prim(tkBool))
      eb  = c.fitExprStrict(c.exprToIL(t, b), prim(tkBool))
      tmp = c.newTemp(prim(tkBool))

    if t[n].kind == SourceKind.And:
      # (And a b) -> (If a b False)
      stmts.add newIf(use(c, ea, stmts),
                      wrap(c, eb, tmp),
                      newAsgn(tmp, newIntVal(0)))

    else:
      # (Or a b) -> (If a True b)
      stmts.add newIf(use(c, ea, stmts),
                      newAsgn(tmp, newIntVal(1)),
                      wrap(c, eb, tmp))

    expr = tmp
    result = prim(tkBool) + {}
  of SourceKind.If:
    let
      (p, b) = t.pair(n) # predicate and body, always present
      cond = openExprToIL(c, t, p)
    if cond.typ.kind != tkBool:
      c.error("`If` condition must be a boolean expression")

    let
      body = exprToIL(c, t, b)
      els = if t.len(n) == 3: exprToIL(c, t, t.child(n, 2))
            else:             unitExpr
      typ = commonType(body.typ, els.typ)
      (fb, fe) =
        case typ.kind
        of tkError:
          c.error("if ($1) and else ($2) branches cannot be unified into a single type" %
                  [$body.typ, $els.typ])
          (body, els)
        else:
          (c.fitExpr(body, typ), c.fitExpr(els, typ))
      tmp = c.newTemp(typ)

    stmts.add newIf(use(c, cond, stmts), wrap(c, fb, tmp), wrap(c, fe, tmp))
    expr = tmp
    result = typ + {}
  of SourceKind.While:
    let (a, b) = t.pair(n)

    c.openScope()
    let
      cond = c.exprToIL(t, a)
      body = c.exprToIL(t, b)
    c.closeScope()

    if cond.typ.kind != tkBool:
      c.error("condition expression must be of type bool")

    if body.typ.kind notin {tkUnit, tkVoid}:
      c.error("`While` body must be a unit or void expression")

    var sub = IrNode(kind: Stmts)
    sub.add newIf(newNot(use(c, cond, sub.children)), newBreak(1))
    sub.add body.stmts
    if body.typ.kind != tkVoid:
      sub.add newDrop(body.expr)

    stmts.add IrNode(kind: Loop, children: @[sub])

    if t[a].kind == SourceKind.Ident and t.getString(a) == "true":
      # it's a loop that doesn't exit via non-exception control-flow
      stmts.add newUnreachable()
      result = prim(tkVoid) + {}
    else:
      expr = UnitNode
      result = prim(tkUnit) + {}
  of SourceKind.Call:
    result = callToIL(c, t, n, expr, stmts) + {}
  of SourceKind.ArrayCons:
    let length = t.len(n)
    if length < high(uint32).int:
      var
        elem = prim(tkVoid) # start with the bottom type
        args = newSeq[Expr](length)

      # analyze the elements and compute the common type:
      for i, it in t.pairs(n):
        args[i] = c.exprToIL(t, it)
        if args[i].typ.kind == tkVoid:
          c.error("element cannot be of type 'void'")
          args[i].typ = errorType()

        if elem.kind != tkError:
          elem = commonType(elem, args[i].typ)
          if elem.kind == tkError and args[i].typ.kind != tkError:
            c.error("cannot unify types")

      result = arrayType(length, elem) + {}
      expr = c.newTemp(result.typ)

      # emit the assignments:
      for i, it in args.pairs:
        stmts.add newAsgn(
          newAt(expr, newIntVal(i)),
          c.use(c.fitExpr(it, elem), stmts))
    else:
      # don't bother analyzing all those elements...
      c.error("array must not exceed 2^32 elements")
      result = errorType() + {}
  of SourceKind.TupleCons:
    if t.len(n) > 0:
      var elems = newSeq[SemType](t.len(n))
      # there are no tuple constructors in the target IL; all elements are
      # assigned individually
      let tmp = c.newTemp(errorType())
      for i, it in t.pairs(n):
        var e = c.exprToIL(t, it)
        if e.typ.kind == tkVoid:
          c.error("tuple element cannot be 'void'")
          # turn into an error expression:
          e.typ = errorType()
          e.expr = IrNode(kind: None)

        elems[i] = e.typ
        # add an assignment for the field:
        stmts.add newAsgn(newFieldExpr(tmp, i), use(c, e, stmts))

      # now that we know the type, correct it:
      c.locals[tmp.id] = SemType(kind: tkTuple, elems: elems)

      expr = tmp
      result = c.locals[tmp.id] + {}
    else:
      # it's the unit value
      expr = UnitNode
      result = prim(tkUnit) + {}
  of SourceKind.RecordCons:
    var
      typ = SemType(kind: tkRecord)
      elems = newSeq[(string, Expr)]()

    for it in t.items(n):
      let
        (nameN, elemN) = t.pair(it)
        name = t.getString(nameN)

      var e = c.exprToIL(t, elemN)
      if e.typ.kind == tkVoid:
        c.error("field type cannot be void")
        # turn into an error expression:
        e.typ = errorType()
        e.expr = IrNode(kind: None)

      if find(typ, name) != -1:
        c.error("record already has field with name " & name)
      else:
        # make sure to keep the lexicographic order
        typ.fields.insert((name, e.typ), lowerBound(typ.fields, name,
          proc(a: auto, b: auto): int = cmp(a.name, b)))

      elems.add (name, e)

    expr = c.newTemp(typ)

    for (name, elem) in elems.items:
      stmts.add newAsgn(newFieldExpr(expr, find(typ, name)), c.use(elem, stmts))

    result = typ + {}
  of SourceKind.Seq:
    if t[n, 0].kind == SourceKind.StringVal:
      # it's a string constructor
      result = SemType(kind: tkSeq, elems: @[prim(tkChar)]) + {}
      let
        str {.cursor.} = t.getString(t.child(n, 0))
        elem = prim(tkChar)
        tmp = c.newTemp(result.typ)
        payloadField = newFieldExpr(tmp, 1)

      # emit the length field assignment:
      stmts.add newAsgn(newFieldExpr(tmp, 0), newIntVal(str.len))

      # emit the payload field assignment:
      if str.len > 0:
        let size = size(prim(tkInt)) + paddedSize(elem) * str.len
        stmts.add newAsgn(payloadField,
          newAllocCall(newIntVal(size), newIntVal(alignment(elem))))

        let payloadExpr = newDeref(c.genPayloadType(elem), payloadField)
        # emit the capacity assignment:
        stmts.add newAsgn(newFieldExpr(payloadExpr, 0), newIntVal(str.len))

        # assign the bytes one by one:
        for i, it in str.pairs:
          stmts.add newAsgn(
            newAt(newFieldExpr(payloadExpr, 1), newIntVal(i)),
            newIntVal(ord(it)))
      else:
        # an empty sequence, set the payload pointer to zero (nil)
        stmts.add newAsgn(payloadField, newIntVal(0))

      expr = tmp
      return

    let
      typ = c.expectNot(c.evalType(t, t.child(n, 0)), tkVoid)
      length = t.len(n) - 1
    var elems = newSeq[IrNode](length)

    # assign all elements to temporaries first, so that the payload is only
    # allocated when control-flow reaches past the argument expressions
    block:
      var i = 0
      for it in t.items(n, 1):
        elems[i] = c.capture(c.fitExpr(c.exprToIL(t, it), typ), stmts)
        inc i

    result = SemType(kind: tkSeq, elems: @[typ]) + {}

    let
      tmp = c.newTemp(result.typ)
      payloadField = newFieldExpr(tmp, 1)

    # emit the length field assignment:
    stmts.add newAsgn(newFieldExpr(tmp, 0), newIntVal(length))

    # emit the payload field assignment:
    if length > 0:
      let size = align(size(prim(tkInt)), alignment(typ)) +
                 (paddedSize(typ) * length)
      # the size of the payload is sizeof(capacity) + sizeof(element) * length
      stmts.add newAsgn(payloadField,
        newAllocCall(newIntVal(size), newIntVal(alignment(typ))))

      let payloadExpr = newDeref(c.genPayloadType(typ), payloadField)
      # emit the capacity assignment:
      stmts.add newAsgn(newFieldExpr(payloadExpr, 0), newIntVal(length))

      # emit the final assignments:
      for i, it in elems.pairs:
        stmts.add newAsgn(
          newAt(newFieldExpr(payloadExpr, 1), newIntVal(i)),
          it)
    else:
      # an empty sequence, set the payload pointer to zero (nil)
      stmts.add newAsgn(payloadField, newIntVal(0))

    expr = tmp
  of SourceKind.FieldAccess:
    let
      (a, b) = t.pair(n)
      tup = c.exprToIL(t, a)
    case tup.typ.kind
    of tkTuple:
      if t[b].kind == SourceKind.IntVal:
        let idx = t.getInt(b)
        if idx >= 0 and idx < tup.typ.elems.len:
          result = tup.typ.elems[idx] + tup.attribs
          expr = newFieldExpr(inlineLvalue(c, tup, stmts), idx.int)
        else:
          c.error("tuple has no element with index " & $idx)
          result = errorType() + {Lvalue, Mutable}
      else:
        c.error("field selector must be an immediate integer")
        result = errorType() + {Lvalue, Mutable}
    of tkRecord:
      if t[b].kind == SourceKind.Ident:
        let idx = find(tup.typ, t.getString(b))
        if idx >= 0:
          result = tup.typ.fields[idx].typ + tup.attribs
          expr = newFieldExpr(inlineLvalue(c, tup, stmts), idx.int)
        else:
          c.error("record has no field with name '$1'" % [t.getString(b)])
          result = errorType() + {Lvalue, Mutable}
      else:
        c.error("field selector must be an identifier")
        result = errorType() + {Lvalue, Mutable}
    of tkError:
      result = tup.typ + {}
    else:
      c.error("expected 'tuple' value")
      result = errorType() + {}
  of SourceKind.At:
    let
      (a, b) = t.pair(n)
      arr = c.exprToIL(t, a)
      idx = c.exprToIL(t, b)

    if arr.typ.kind notin {tkSeq, tkArray, tkTuple, tkError}:
      c.error("expected 'seq', 'array' or 'tuple' value")
    if idx.typ.kind notin {tkInt, tkError}:
      c.error("index expression must be of type 'int'")

    case arr.typ.kind
    of tkSeq:
      result = arr.typ.elems[0] + arr.attribs

      let at = c.getTypeBoundOp(opAt, arr.typ)
      # keep the following things in mind:
      # * the statements for the arr expression (i.e., its side effects),
      #   need to come first
      # * the result of the index expression needs to be captured, as it could
      #   be impure and there might still be outermore side-effectful
      #   expressions
      # * checking the index and computing the address *must* be part of
      #   the `expr`, otherwise side-effects from outermore index expressions
      #   could render the array stale
      expr = newDeref(c.typeToIL(result.typ),
        newCall(at, @[c.inlineLvalue(arr, stmts), c.capture(idx, stmts)]))
    of tkArray:
      result = arr.typ.elem[0] + arr.attribs

      # works the same as a seq access, just without the payload indirection
      let
        at = c.getTypeBoundOp(opAt, arr.typ)
        res = newCall(at, @[newAddr(c.inlineLvalue(arr, stmts)),
                            c.capture(idx, stmts)])
      if Lvalue in arr.attribs:
        # use deferred evaluation
        expr = newDeref(c.typeToIL(result.typ), res)
      else:
        # evaluate the access eagerly
        let tmp = c.newTemp(prim(tkPointer))
        stmts.add newAsgn(tmp, res)
        expr = newDeref(c.typeToIL(result.typ), tmp)
    of tkTuple:
      let (typ, _) = unionOf(arr.typ.elems)
      # the result is neither mutable nor is it an lvalue, but lvalue-ness
      # currently has to be preserved for the enclosing `At` access to
      # produce the right IL code
      result = typ + (arr.attribs * {Lvalue})

      let at = c.getTypeBoundOp(opAt, arr.typ)
      # while not yielding a mutable lvalue, dynamic tuple access has the same
      # evaluation order as seq access
      let
        tmp = c.newTemp(typ)
        res = newCall(at, @[c.inlineLvalue(arr, stmts), c.capture(idx, stmts),
                            newAddr(tmp)])
      if Lvalue in arr.attribs:
        # use deferred evaluation for the actual tuple access (including the
        # index check)
        expr = newDeref(c.typeToIL(result.typ), res)
      else:
        # evaluate the access eagerly
        stmts.add newDrop(res)
        expr = tmp
    else:
      result = errorType() + arr.attribs
  of SourceKind.As:
    let
      (a, b) = t.pair(n)
      e = c.exprToIL(t, a)
      typ = c.expectNot(c.evalType(t, b), tkVoid)
    # a copy must always be created, even when there's no widening going on
    if e.typ == typ:
      expr = use(c, e, stmts)
    else:
      expr = inline(c.fitExpr(e, typ), stmts)
    result = typ + {} # lvalue-ness and mutability are discarded
  of SourceKind.Asgn:
    let (a, b) = t.pair(n)
    var dst = c.exprToIL(t, a)
    if {Lvalue, Mutable} * dst.attribs < {Lvalue, Mutable}:
      c.error("LHS expression must be a mutable l-value expression")
      dst.expr = IrNode(kind: None)

    let src = c.fitExpr(c.exprToIL(t, b), dst.typ)
    stmts.add newAsgn(inline(dst, stmts), use(c, src, stmts))

    expr = UnitNode
    result = prim(tkUnit) + {}
  of SourceKind.Return:
    var e =
      case t.len(n)
      of 0: unitExpr
      of 1: c.exprToIL(t, t.child(n, 0))
      else: unreachable() # syntax error

    if e.typ.kind == tkVoid:
      c.error("cannot return 'void' expression")
      e.typ = prim(tkError)

    # apply the necessary to-supertype conversions:
    e = c.fitExpr(e, c.retType)
    stmts.add newReturn(use(c, e, stmts))

    result = prim(tkVoid) + {}
  of SourceKind.Unreachable:
    stmts.add newUnreachable()
    result = prim(tkVoid) + {}
  of SourceKind.Match:
    var e = c.exprToIL(t, t.child(n, 0))
    if e.typ.kind notin {tkUnion, tkError}:
      c.error("expression must be of union type")
      e.typ = errorType()

    var
      got = newSeq[SemType]() ## the handled types
      handlers = newSeq[tuple[local: IrNode, body: Expr]]()
      res = prim(tkVoid) # start with the bottom type

    # the type of the Match expression is the least upper bound between all
    # handlers. Thus, analysis has to happen in two passes: the first one
    # analyses all handlers, and the second one does the fitting and generates
    # the dispatcher
    for it in t.items(n, 1):
      let
        (pat, bodyNode) = t.pair(it)
        typ = c.expectNot(c.evalType(t, t.child(pat, 1)), tkVoid)
        at = lowerBound(got, typ, cmp)

      c.openScope()
      let name {.cursor.} = t.getString(t.child(pat, 0))
      if c.lookup(name).kind != ekNone:
        c.error("redeclaration of '$1'" % [name])
      let tmp = c.newTemp(typ)
      c.addDecl(name, Entity(kind: ekValue, id: tmp.id.int))
      let body = c.exprToIL(t, bodyNode)
      c.closeScope()

      let newResult = commonType(res, body.typ)
      if tkError notin {res.kind, body.typ.kind} and
         newResult.kind == tkError:
        c.error("'$1' and '$2' cannot be unified into a single type" %
                [$res, $body.typ])
      res = newResult

      if at >= got.len or got[at] != typ:
        got.insert typ, at
        handlers.add (tmp, body)
      else:
        c.error("duplicate handler for '$1'" % [$typ])

    expr = c.newTemp(res)

    # second pass:
    if e.typ.kind == tkUnion:
      let target = capture(c, e, stmts) ## the union to match against
      var handled: int
      # XXX: the IL require the selector expression for a case statement to
      #      be a simple expression (which a field expression is not), hence
      #      the intermediate temporary
      let sel = c.newTemp(prim(tkInt))
      stmts.add newAsgn(sel, newFieldExpr(target, 0))
      var caseStmt = newCase(c.typeToIL(prim(tkInt)), sel)
      for i, it in handlers.pairs:
        let idx = e.typ.elems.find(c.locals[it.local.id])
        if idx != -1:
          var body = IrNode(kind: Stmts)
          body.add newAsgn(it.local, newFieldExpr(newFieldExpr(target, 1), idx))
          body.add wrap(c, c.fitExpr(it.body, res), expr).children
          caseStmt.add newChoice(newIntVal(idx), body)
          inc handled
        else:
          c.error("'$1' is not part of '$2'" %
                  [$c.locals[it.local.id], $e.typ])

      if handled != e.typ.elems.len:
        # not all types in the union have a matching handler
        for it in e.typ.elems.items:
          if find(got, it) == -1:
            c.error("a matcher for '$1' is missing" % [$it])

      stmts.add caseStmt

    result = res + {}
  of SourceKind.Exprs:
    let last = t.len(n) - 1
    var seenVoidExpr = false
    template voidGuard(body: untyped) =
      if not seenVoidExpr:
        body
    for i, si in t.pairs(n):
      let e = c.openExprToIL(t, si)
      voidGuard:
        stmts.add e.stmts
      if i == last:
        voidGuard:
          result = e.typ + e.attribs
          case e.typ.kind
          of tkVoid: discard "okay, nothing to do"
          else:      expr = e.expr
      else:
        case e.typ.kind
        of tkVoid:
          result = e.typ + e.attribs
          seenVoidExpr = true # check, but drop further stmts & exprs
        of tkUnit:
          voidGuard:
            stmts.add newDrop(e.expr)
        else:
          c.error("non-trailing expressions must be unit or void, got: $1" %
                    [$e.typ])
          voidGuard:
            stmts.add newDrop(e.expr) # error correction
  of SourceKind.Decl:
    localDeclToIL(c, t, n, stmts)
    expr = UnitNode
    result = prim(tkUnit) + {}
  of AllNodes - ExprNodes:
    unreachable($t[n].kind)

proc importIoProcedures(c) =
  ## Adds the built-in I/O procedures to `c`.
  # both 'write' and 'writeErr' need a wrapper procedure, as the external
  # procedure cannot take a seq as input (only a pointer and an int)
  var procTy = SemType(kind: tkProc,
                       elems: @[prim(tkVoid), prim(tkPointer), prim(tkInt)])
  let writeHostPrc = c.addProc(procTy):
    buildTree Import:
      bu.add Node(kind: Type, val: c.genProcType(procTy))
      bu.add Node(kind: StringVal, val: c.literals.pack("core.write"))
  let writeErrHostPrc = c.addProc(procTy):
    buildTree Import:
      bu.add Node(kind: Type, val: c.genProcType(procTy))
      bu.add Node(kind: StringVal, val: c.literals.pack("core.writeErr"))
  procTy = SemType(kind: tkProc,
                    elems: @[prim(tkInt), prim(tkPointer), prim(tkInt)])
  let fileSizePrc = c.addProc(procTy):
    buildTree Import:
      bu.add Node(kind: Type, val: c.genProcType(procTy))
      bu.add Node(kind: StringVal, val: c.literals.pack("core.fileSize"))
  procTy = SemType(kind: tkProc,
                   elems: @[prim(tkInt), prim(tkPointer), prim(tkInt),
                            prim(tkPointer), prim(tkInt)])
  let readFileHostPrc = c.addProc(procTy):
    buildTree Import:
      bu.add Node(kind: Type, val: c.genProcType(procTy))
      bu.add Node(kind: StringVal, val: c.literals.pack("core.readFile"))

  # both write and writeErr use the same wrapper body, just with a different
  # external procedure to call
  const Body = """
    (ProcDef (Type $1)
      (Params (Local 0))
      (Locals (Type $2))
      (Stmts
        (If
          (Lt (Type $4)
            (IntVal 0)
            (Copy (Field (Local 0) 0)))
          (Call (Proc $3)
            (Addr
              (At
                (Field
                  (Deref (Type $5)
                    (Copy (Field (Local 0) 1))) 1)
                (IntVal 0)))
            (Copy (Field (Local 0) 0))))
        (Return (IntVal 0))))
  """

  let stringType = SemType(kind: tkSeq, elems: @[prim(tkChar)])
  procTy = SemType(kind: tkProc, elems: @[prim(tkUnit), stringType])
  let
    signature = c.genProcType(procTy)
    strTypeIL = c.typeToIL(stringType)
    intTypeIL = c.typeToIL(prim(tkInt))
    payloadType = c.genPayloadType(prim(tkChar))

  let writePrc = c.addProc(procTy):
    parseSexp[NodeKind](Body % [$signature, $strTypeIL, $writeHostPrc,
                                $intTypeIL, $payloadType],
                        c.literals)
  c.addDecl("write", Entity(kind: ekProc, id: writePrc))

  let writeErrPrc = c.addProc(procTy):
    parseSexp[NodeKind](Body % [$signature, $strTypeIL, $writeErrHostPrc,
                                $intTypeIL, $payloadType],
                        c.literals)
  c.addDecl("writeErr", Entity(kind: ekProc, id: writeErrPrc))

  # build the readFile procedure, which is a wrapper around the external
  # `fileSize` and `readFile` core procedures. It works as follows:
  # 1. query the size of the file
  # 2. create a sequence fitting N characters (N is the result of the previous
  #    size query)
  # 3. read N bytes from the file
  # 4. truncate the sequence to the number of actually read bytes
  # The file is not locked for the duration of the whole operation, and thus
  # it's possible (though unlikely) for the file to change in-between the size
  # query and read. While not ideal, the truncation takes care of that case.
  # XXX: in the future, the use of a handle-based file core API will resolve
  #      this problem
  var readFileBody = IrNode(kind: Stmts)
  readFileBody.add newAsgn(newFieldExpr(newLocal(1), 0),
    newCall(fileSizePrc.uint32, @[
      newAddr(newFieldExpr(c.genPayloadAccess(newLocal(0), stringType), 1)),
      newFieldExpr(newLocal(0), 0)]))
  readFileBody.add newAsgn(newFieldExpr(newLocal(1), 1),
    newAllocCall(
      c.newIntOp(Add,
        newIntVal(size(prim(tkInt))),
        newFieldExpr(newLocal(1), 0)),
      newIntVal(payloadAlignment(stringType.elems[0]))))
  readFileBody.add newAsgn(newFieldExpr(newLocal(1), 0),
    newCall(readFileHostPrc.uint32, @[
      newAddr(newFieldExpr(c.genPayloadAccess(newLocal(0), stringType), 1)),
      newFieldExpr(newLocal(0), 0),
      newAddr(newFieldExpr(c.genPayloadAccess(newLocal(1), stringType), 1)),
      newFieldExpr(newLocal(1), 0)]))
  readFileBody.add newReturn(newLocal(1))

  procTy = SemType(kind: tkProc, elems: @[stringType, stringType])
  let readFilePrc = c.addProc(procTy):
    buildTree ProcDef:
      bu.add Node(kind: Type, val: c.genProcType(procTy))
      bu.subTree Params:
        bu.add Node(kind: Local, val: 0)
      bu.subTree Locals:
        bu.add Node(kind: Type, val: c.typeToIL(stringType))
        bu.add Node(kind: Type, val: c.typeToIL(stringType))
      convert(readFileBody, c.literals, bu)
  c.addDecl("readFile", Entity(kind: ekProc, id: readFilePrc))

proc open*(reporter: sink(ref ReportContext[string])): ModuleCtx =
  ## Creates a new empty module translation/analysis context.
  result = ModuleCtx(reporter: reporter,
                     types: initBuilder[NodeKind](TypeDefs),
                     globals: initBuilder[NodeKind](GlobalDefs),
                     exports: initBuilder[NodeKind](List),
                     # start with the top-level scope
                     scopes: @[default(Scope)],
                     entry: -1)

  template c: untyped = result

  # XXX: the maximum amount of heap memory is currently static and allocated
  #      up-front
  const
    StackSize = 1024 * 4        # 4 KiB
    HeapSize  = 1024 * 1024 * 4 # 4 MiB

  let heapType = c.addType Array:
    c.types.add Node(kind: Immediate, val: HeapSize) # size-in-bytes
    c.types.add Node(kind: Immediate, val: 8)        # alignment
    c.types.add Node(kind: Immediate, val: HeapSize) # count
    c.types.add Node(kind: UInt, val: 1)

  # globals and their meaning:
  # * 0: size of the stack (a constant)
  # * 1: size of the heap (a constant)
  # * 2: the heap region, represented as an array of bytes
  # * 3: heap management data
  c.globals.subTree GlobalDef:
    c.globals.add Node(kind: UInt, val: 8)
    c.globals.add Node(kind: IntVal, val: StackSize)
  c.globals.subTree GlobalDef:
    c.globals.add Node(kind: Int, val: 8)
    c.globals.add Node(kind: IntVal, val: HeapSize)
  c.globals.subTree GlobalLoc:
    c.globals.add Node(kind: Type, val: heapType)
    c.globals.subTree Data:
      c.globals.add Node(kind: Type, val: heapType)
  c.globals.subTree GlobalLoc:
    c.globals.add Node(kind: Int, val: 8)
    c.globals.subTree Data:
      c.globals.add Node(kind: Int, val: 8)
  # XXX: the heap managment data and heap size should both use UInt, but
  #      pointer arithmetic in the target IL is a bit fuzzy at the moment

  c.exports.subTree Export:
    c.exports.add Node(kind: StringVal, val: c.literals.pack("stack_size"))
    c.exports.add Node(kind: Global, val: 0)

  # add the built-in allocator and seq procedures
  # XXX: these need to be provided by a system-like module in the future

  template addProc(typ: SemType, body: string, args: untyped) =
    discard addProc(result, typ, parseSexp[NodeKind](body % args, c.literals))

  # the allocator uses a simple bump-pointer allocation scheme where memory
  # is never freed for re-use. When the heap memory is exhausted, an
  # exception/panic is raised
  const AllocBody = """
    (ProcDef (Type $1)
      (Params (Local 0) (Local 2))
      (Locals (Type $2) (Type $2) (Type $2))
      (Stmts
        (Asgn (Local 1) (Copy (Global 3)))
        (Asgn (Local 1)
          (BitAnd (Type $2)
            (Add (Type $2)
              (Copy (Local 1))
              (Sub (Type $2)
                (Copy (Local 2))
                (IntVal 1)))
            (BitNot (Type $2)
              (Sub (Type $2)
                (Copy (Local 2))
                (IntVal 1)))))
        (If
          (Le (Type $2)
            (Add (Type $2)
              (Copy (Local 0))
              (Copy (Local 1)))
            (Copy (Global 1)))
          (Stmts
            (Asgn (Global 3)
              (Add (Type $2)
                (Copy (Local 1))
                (Copy (Local 0))))
            (Return
              (Addr
                (At (Global 2) (Copy (Local 1))))))
          (Raise (IntVal 0)))))
  """
  var procTy = SemType(kind: tkProc,
                       elems: @[prim(tkPointer), prim(tkInt), prim(tkInt)])
  addProc procTy, AllocBody,
          [$c.genProcType(procTy), $c.typeToIL(prim(tkInt))]

  const DeallocBody = """
    (ProcDef (Type $1)
      (Params (Local 0))
      (Locals (Type $2))
      (Return (IntVal 0)))
  """
  procTy = SemType(kind: tkProc, elems: @[prim(tkUnit), prim(tkPointer)])
  addProc procTy, DeallocBody,
          [$c.genProcType(procTy), $c.typeToIL(prim(tkInt))]

  # realloc(ptr: pointer, oldsize: int, newsize: int, align: int) -> pointer
  const ReallocBody = """
    (ProcDef (Type $1)
      (Params (Local 0) (Local 1) (Local 2) (Local 4))
      (Locals (Type $2) (Type $2) (Type $2) (Type $2) (Type $2))
      (If
        (Eq (Type $2)
          (Copy (Local 0))
          (IntVal 0))
        (Return (Call (Proc 0)
          (Copy (Local 2))
          (Copy (Local 4))))
        (Stmts
          (Asgn (Local 3)
            (Call (Proc 0)
              (Copy (Local 2))
              (Copy (Local 4))))
          (Blit (Copy (Local 3)) (Copy (Local 0)) (Copy (Local 1)))
          (Drop (Call (Proc 1) (Copy (Local 0))))
          (Return (Copy (Local 3))))
        )
      )
  """
  procTy = SemType(kind: tkProc,
                   elems: @[prim(tkPointer), prim(tkPointer), prim(tkInt),
                            prim(tkInt), prim(tkInt)])
  addProc procTy, ReallocBody,
          [$c.genProcType(procTy), $c.typeToIL(prim(tkInt))]

  # grow(payload: pointer, capacity: int, stride: int, align: int) -> pointer
  # reallocates the given payload if its capacity is less than the requested
  # one. The new payload is returned
  const GrowBody = """
    (ProcDef (Type $1)
      (Params (Local 0) (Local 1) (Local 2) (Local 3))
      (Locals (Ptr) (Type $2) (Type $2) (Type $2))
      (Stmts
        (If
          (Lt (Type $2)
            (Copy (Local 3))
            (IntVal 8))
          (Asgn (Local 3) (IntVal 8)))
        (If
          (Eq (Type $2)
            (Copy (Local 0))
            (IntVal 0))
          (Asgn (Local 0)
            (Call (Proc 0)
              (Add (Type $2)
                (IntVal $3)
                (Mul (Type $2)
                  (Copy (Local 1))
                  (Copy (Local 2))))
              (Copy (Local 3))))
          (If
            (Not
              (Lt (Type $2)
                (Load (Type $2)
                  (Copy (Local 0)))
                (Copy (Local 1))))
            (Asgn (Local 0)
              (Call (Proc 2)
                (Copy (Local 0))
                (Add (Type $2)
                  (IntVal $3)
                  (Mul (Type $2)
                    (Load (Type $2)
                      (Copy (Local 0)))
                    (Copy (Local 2))))
                (Add (Type $2)
                  (IntVal $3)
                  (Mul (Type $2)
                    (Copy (Local 1))
                    (Copy (Local 2))))
                (Copy (Local 3))))))
        (Store (Type $2)
          (Copy (Local 0))
          (Copy (Local 1)))
        (Return (Copy (Local 0)))))
  """
  addProc procTy, GrowBody,
          [$c.genProcType(procTy), $c.typeToIL(prim(tkInt)),
           $size(prim(tkInt)) #[<- offset of payload's data field]#]

  # prepareAdd(lenAddr: pointer, payloadAddr: pointer, stride: int, align: int) -> pointer
  # increments the length and resizes the payload (via the grow procedure)
  # when needed. The implementation works with all seq types in order to not
  # having to synthesize a version for each used seq type
  const PrepareAddBody = """
    (ProcDef (Type $1)
      (Params (Local 0) (Local 1) (Local 2) (Local 4))
      (Locals (Ptr) (Ptr) (Type $2) (Type $2) (Type $2))
      (Stmts
        (Asgn (Local 3)
          (Load (Type $2)
            (Copy (Local 0))))
        (Store (Type $2)
          (Copy (Local 0))
          (Add (Type $2)
            (Copy (Local 3))
            (IntVal 1)))
        (Store (Ptr)
          (Copy (Local 1))
          (Call (Proc 3)
            (Load (Ptr)
              (Copy (Local 1)))
            (Load (Type $2)
              (Copy (Local 0)))
            (Copy (Local 2))
            (Copy (Local 4))))
        (Return
          (Reinterp (Ptr) (Type $2)
            (Add (Type $2)
              (Reinterp (Type $2) (Ptr)
                (Load (Ptr)
                  (Copy (Local 1))))
              (Add (Type $2)
                (IntVal $3)
                (Mul (Type $2)
                  (Copy (Local 3))
                  (Copy (Local 2)))))))))
  """
  addProc procTy, PrepareAddBody,
          [$c.genProcType(procTy), $c.typeToIL(prim(tkInt)),
           $size(prim(tkInt)) #[<- offset of payload's data field]#]

  importIoProcedures(result)

proc close*(c: sink ModuleCtx): PackedTree[NodeKind] =
  ## Closes the module context and returns the accumulated translated code.
  var bu = initBuilder[NodeKind]()
  bu.subTree Module:
    bu.add finish(move c.types)
    bu.add finish(move c.globals)
    bu.subTree ProcDefs:
      for it in c.procs.items:
        bu.add it
    let exports = finish(move c.exports)
    if exports.len > 1: # don't add an empty export list
      bu.add exports

  initTree[NodeKind](finish(bu), c.literals)

proc exprToIL*(c; t): SemType =
  ## Translates the given source language expression to the highest-level IL
  ## and turns it into a procedure. Also returns the type of the expression.
  var e = c.exprToIL(t, NodeIndex(0))
  result = e.typ

  defer:
    c.resetProcContext()

  if result.kind == tkError:
    return # don't create any procedure

  let
    procTy    = procType(result)
    signature = c.genProcType(procTy)

  let body = buildTree ProcDef:
    bu.add Node(kind: Type, val: signature)
    bu.subTree Params:
      for i in 0..<numILParams(procTy):
        bu.add Node(kind: Local, val: i.uint32)
    bu.subTree Locals:
      for it in c.locals.items:
        bu.add Node(kind: Type, val: c.typeToIL(it))
    bu.subTree Stmts:
      # first emit all statements:
      for it in e.stmts.items:
        convert(it, c.literals, bu)

      # then the expression:
      if e.typ.kind != tkVoid:
        bu.subTree Return:
          use(e.expr, c.literals, bu)

  c.procs.add body
  c.procList.add ProcInfo(typ: procTy)
  c.entry = c.procList.high
  # add the procedure as an export, to be able to look it up from the outside
  c.exports.subTree Export:
    let id = c.procList.high
    c.exports.add Node(kind: StringVal, val: c.literals.pack("expr." & $id))
    c.exports.add Node(kind: Proc, val: id.uint32)

proc declToIL*(c; t; n: NodeIndex) =
  ## Translates the given source language declaration to the target IL.
  ## On success, the declaration effects are applied to `c` and the declared
  ## procedure's return type is returned.
  case t[n].kind
  of SourceKind.ProcDecl:
    let name = t.getString(t.child(n, 0))
    if c.lookup(name).kind != ekNone:
      c.error("redeclaration of '" & name & "'")
      return

    c.retType = evalType(c, t, t.child(n, 1))

    defer:
      c.resetProcContext() # clear the context again

    var procTy = procType(c.retType)

    # add the parameter types to the proc type:
    for it in t.items(t.child(n, 2)):
      procTy.elems.add c.expectNot(evalType(c, t, t.child(it, 1)), tkVoid)

    let signature = c.genProcType(procTy)

    # register the proc before analysing/translating the body. The real IL
    # body is filled in once complete
    let self = c.addProc(procTy, @[])
    c.addDecl(name, Entity(kind: ekProc, id: self))

    c.openScope()
    # add the parameters to the scope:
    for i, it in t.pairs(t.child(n, 2)):
      let name = t.getString(t.child(it, 0))
      if c.lookup(name).kind != ekNone:
        c.error("redeclaration of '" & name & "'")

      # add the local and register the entity regadless of whether there was
      # an error
      c.locals.add procTy.elems[i + 1]

      c.params.add (procTy.elems[i + 1], c.locals.high.uint32)
      c.addDecl(name, Entity(kind: ekParam, id: c.params.high))

    # analyse the body:
    var e = c.fitExpr(c.exprToIL(t, t.child(n, 3)), c.retType)
    c.closeScope()

    if e.typ.kind != tkVoid:
      # force into a void expression by appending a return statement
      e.stmts.add newReturn(move e.expr)
      e.typ = prim(tkVoid)

    var bu = initBuilder[NodeKind](ProcDef)
    bu.add Node(kind: Type, val: signature)
    bu.subTree Params:
      for i in 0..<numILParams(procTy):
        bu.add Node(kind: Local, val: i.uint32)
    bu.subTree Locals:
      for it in c.locals.items:
        bu.add Node(kind: Type, val: c.typeToIL(it))
    # add the body:
    bu.subTree Stmts:
      for it in e.stmts.items:
        convert(it, c.literals, bu)

    c.procs[self] = finish(bu)
    c.entry = self
    # add the user-defined procedure as an export, to be able to look it up
    # from the outside
    c.exports.subTree Export:
      # prefix with `module.` so that the name cannot collide with foreign
      # procedure names (which use their own prefix)
      c.exports.add Node(kind: StringVal,
                         val: c.literals.pack("module." & name))
      c.exports.add Node(kind: Proc, val: self.uint32)
  of SourceKind.TypeDecl:
    let name = t.getString(t.child(n, 0))
    if c.lookup(name).kind != ekNone:
      c.error("redeclaration of '" & name & "'")
      return

    let typ = evalType(c, t, t.child(n, 1))
    # add the type to the scope, regardless of whether `typ` is an error
    c.aliases.add typ
    c.addDecl(name, Entity(kind: ekType, id: c.aliases.high))
  of AllNodes - DeclNodes:
    unreachable() # syntax error
