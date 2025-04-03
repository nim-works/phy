## Implements pretty-printing for source-language types.

import
  experimental/[
    sexp
  ],
  phy/[
    types
  ],
  vm/utils

proc typeToString*(typ: SemType): string =
  ## Returns the text representation of `typ` meant for diagnostic messages
  ## and test output.
  case typ.kind
  of tkVoid:  "void"
  of tkUnit:  "unit"
  of tkBool:  "bool"
  of tkChar:  "char"
  of tkInt:   "int"
  of tkFloat: "float"
  of tkTuple:
    var res = "("
    for i, it in typ.elems.pairs:
      if i > 0:
        res.add ", "
      res.add typeToString(it)

    if typ.elems.len == 1:
      res.add ","
    res.add ")"
    res
  of tkRecord:
    var res = "{"
    for i, it in typ.fields.pairs:
      if i > 0:
        res.add ", "
      res.add it.name
      res.add " : "
      res.add typeToString(it.typ)
    res.add "}"
    res
  of tkUnion:
    var res = "union("
    for i, it in typ.elems.pairs:
      if i > 0:
        res.add ", "
      res.add typeToString(it)
    res.add ")"
    res
  of tkProc:
    var res = "proc("
    for i, it in typ.elems.toOpenArray(1, typ.elems.high).pairs:
      if i > 0:
        res.add ", "
      res.add typeToString(it)
    res.add ") -> "
    res.add typeToString(typ.elems[0])
    res
  of tkSeq:
    "seq(" & typeToString(typ.elems[0]) & ")"
  of tkError:
    # diagnostic messages should not show error types, therefore rendering is
    # not implemented for them. If control-flow reaches here, it usually means
    # that a guard against error types is missing somewhere
    unreachable()

proc `$`*(typ: SemType): string =
  ## A shortcut for `typeToString <#typeToString,SemType>`_.
  typeToString(typ)

proc typeToSexp*(typ: SemType): SexpNode =
  ## Returns the S-expression of the AST representing the type construction
  ## for `typ`.
  case typ.kind
  of tkVoid:  newSList(newSSymbol("VoidTy"))
  of tkUnit:  newSList(newSSymbol("UnitTy"))
  of tkBool:  newSList(newSSymbol("BoolTy"))
  of tkChar:  newSList(newSSymbol("CharTy"))
  of tkInt:   newSList(newSSymbol("IntTy"))
  of tkFloat: newSList(newSSymbol("FloatTy"))
  of tkTuple:
    var res = newSList(newSSymbol("TupleTy"))
    for it in typ.elems.items:
      res.add typeToSexp(it)
    res
  of tkRecord:
    var res = newSList(newSSymbol("RecordTy"))
    for it in typ.fields.items:
      res.add newSList(newSSymbol("Field"),
                       newSSymbol(it.name),
                       typeToSexp(it.typ))
    res
  of tkUnion:
    var res = newSList(newSSymbol("UnionTy"))
    for it in typ.elems.items:
      res.add typeToSexp(it)
    res
  of tkProc:
    var res = newSList(newSSymbol("ProcTy"))
    for it in typ.elems.items:
      res.add typeToSexp(it)
    res
  of tkSeq:
    newSList(newSSymbol("SeqTy"), typeToSexp(typ.elems[0]))
  of tkError:
    unreachable()
