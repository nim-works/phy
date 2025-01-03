## Implements pretty-printing for source-language types.

import
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
