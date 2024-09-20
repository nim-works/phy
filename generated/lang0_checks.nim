# Generated by the passtool; do not modify
import passes/trees
import passes/spec

type
  Tree = PackedTree[NodeKind]
  Error = object
    pos: NodeIndex
    rule: string
    node: NodeIndex
    child: int

template setError(e, n: NodeIndex; c: int; r: string) =
  if ord(err.pos) < ord(e):
    err = Error(pos: e, rule: r, node: n, child: c)

proc matchAtom(tree: Tree; n: var NodeIndex; kind: NodeKind): bool =
  result = n in tree and tree[n].kind == kind
  if result:
    n = tree.next(n)

template matchTree(rule: string; k: NodeKind; label, body: untyped) =
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
        n = save

proc check_type_id*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_type*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_local*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_proc*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_rvalue*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_intval*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_floatval*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_simple*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_value*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_cont_name*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_goto*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_err_goto*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_choice*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_exit*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_stmt*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_continuation*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_procdef*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_globaldef*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_module*(tree: Tree, n: var NodeIndex, err: var Error): bool
proc check_top*(tree: Tree, n: var NodeIndex, err: var Error): bool

proc check_type_id*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Type <int>)", Type, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true

proc check_type*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Int <int>)", Int, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true
  matchTree "(UInt <int>)", UInt, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true
  matchTree "(Float <int>)", Float, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true
  matchTree "(ProcTy (Void) <type_id>*)", ProcTy, match:
    matchTree "(Void)", Void, match:
      discard
    if num == len or not result: break match
    inc num
    while num < len:
      if not check_type_id(tree, n, err): break
      inc num
  if result: return true
  matchTree "(ProcTy <type_id>+)", ProcTy, match:
    var tmp = num
    while num < len:
      if not check_type_id(tree, n, err): break
      inc num
    if tmp == num: break match
  if result: return true

proc check_local*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Local <int>)", Local, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true

proc check_proc*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Proc <int>)", Proc, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true

proc check_rvalue*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Load <type_id> <value>)", Load, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Addr (IntVal ...))", Addr, match:
    matchTree "(IntVal <int>)", IntVal, match:
      if num == len or not matchAtom(tree, n, Immediate): break match
      inc num
    if num == len or not result: break match
    inc num
  if result: return true
  matchTree "(Neg <type_id> <value>)", Neg, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Add <type_id> <value> <value>)", Add, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Sub <type_id> <value> <value>)", Sub, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Mul <type_id> <value> <value>)", Mul, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Div <type_id> <value> <value>)", Div, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Mod <type_id> <value> <value>)", Mod, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(AddChck <type_id> <value> <value> <local>)", AddChck, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_local(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(SubChck <type_id> <value> <value> <local>)", SubChck, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_local(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Not <value>)", Not, match:
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Eq <type_id> <value> <value>)", Eq, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Lt <type_id> <value> <value>)", Lt, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Le <type_id> <value> <value>)", Le, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(BitNot <type_id> <value>)", BitNot, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(BitOr <type_id> <value> <value>)", BitOr, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(BitAnd <type_id> <value> <value>)", BitAnd, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(BitXor <type_id> <value> <value>)", BitXor, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Shl <type_id> <value> <value>)", Shl, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Shr <type_id> <value> <value>)", Shr, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Reinterp <type_id> <type_id> <value>)", Reinterp, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Conv <type_id> <type_id> <value>)", Conv, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Call <proc> <value>*)", Call, match:
    if num == len or not check_proc(tree, n, err): break match
    inc num
    while num < len:
      if not check_value(tree, n, err): break
      inc num
  if result: return true
  matchTree "(Call <type_id> <value>+)", Call, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    var tmp = num
    while num < len:
      if not check_value(tree, n, err): break
      inc num
    if tmp == num: break match
  if result: return true

proc check_intval*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(IntVal <int>)", IntVal, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true

proc check_floatval*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(FloatVal <float>)", FloatVal, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true

proc check_simple*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  if check_intval(tree, n, err): return true
  if check_floatval(tree, n, err): return true
  matchTree "(ProcVal <int>)", ProcVal, match:
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
  if result: return true
  matchTree "(Copy <local>)", Copy, match:
    if num == len or not check_local(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Copy (Global ...))", Copy, match:
    matchTree "(Global <int>)", Global, match:
      if num == len or not matchAtom(tree, n, Immediate): break match
      inc num
    if num == len or not result: break match
    inc num
  if result: return true

proc check_value*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  if check_simple(tree, n, err): return true
  if check_rvalue(tree, n, err): return true

proc check_cont_name*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  if matchAtom(tree, n, Immediate): return true

proc check_goto*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Continue <cont_name>)", Continue, match:
    if num == len or not check_cont_name(tree, n, err): break match
    inc num
  if result: return true

proc check_err_goto*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Unwind)", Unwind, match:
    discard
  if result: return true
  if check_goto(tree, n, err): return true

proc check_choice*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Choice <intval> <goto>)", Choice, match:
    if num == len or not check_intval(tree, n, err): break match
    inc num
    if num == len or not check_goto(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Choice <floatval> <goto>)", Choice, match:
    if num == len or not check_floatval(tree, n, err): break match
    inc num
    if num == len or not check_goto(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Choice <intval> <intval> <goto>)", Choice, match:
    if num == len or not check_intval(tree, n, err): break match
    inc num
    if num == len or not check_intval(tree, n, err): break match
    inc num
    if num == len or not check_goto(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Choice <floatval> <floatval> <goto>)", Choice, match:
    if num == len or not check_floatval(tree, n, err): break match
    inc num
    if num == len or not check_floatval(tree, n, err): break match
    inc num
    if num == len or not check_goto(tree, n, err): break match
    inc num
  if result: return true

proc check_exit*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  if check_goto(tree, n, err): return true
  matchTree "(Continue <cont_name> <value>)", Continue, match:
    if num == len or not check_cont_name(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Loop <cont_name>)", Loop, match:
    if num == len or not check_cont_name(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Unreachable)", Unreachable, match:
    discard
  if result: return true
  matchTree "(Raise <value> <err_goto>)", Raise, match:
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_err_goto(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(SelectBool <value> <goto> <goto>)", SelectBool, match:
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_goto(tree, n, err): break match
    inc num
    if num == len or not check_goto(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Select <type_id> <simple> <choice>+)", Select, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_simple(tree, n, err): break match
    inc num
    var tmp = num
    while num < len:
      if not check_choice(tree, n, err): break
      inc num
    if tmp == num: break match
  if result: return true
  matchTree "(CheckedCall <proc> <value>* <goto> <err_goto>)", CheckedCall, match:
    if num == len or not check_proc(tree, n, err): break match
    inc num
    while num < len:
      if not check_value(tree, n, err): break
      inc num
    if num == len or not check_goto(tree, n, err): break match
    inc num
    if num == len or not check_err_goto(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(CheckedCall <type_id> <value>+ <goto> <err_goto>)", CheckedCall, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    var tmp = num
    while num < len:
      if not check_value(tree, n, err): break
      inc num
    if tmp == num: break match
    if num == len or not check_goto(tree, n, err): break match
    inc num
    if num == len or not check_err_goto(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(CheckedCallAsgn <local> <proc> <value>* <goto> <err_goto>)", CheckedCallAsgn, match:
    if num == len or not check_local(tree, n, err): break match
    inc num
    if num == len or not check_proc(tree, n, err): break match
    inc num
    while num < len:
      if not check_value(tree, n, err): break
      inc num
    if num == len or not check_goto(tree, n, err): break match
    inc num
    if num == len or not check_err_goto(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(CheckedCallAsgn <local> <type_id> <value>+ <goto> <err_goto>)", CheckedCallAsgn, match:
    if num == len or not check_local(tree, n, err): break match
    inc num
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    var tmp = num
    while num < len:
      if not check_value(tree, n, err): break
      inc num
    if tmp == num: break match
    if num == len or not check_goto(tree, n, err): break match
    inc num
    if num == len or not check_err_goto(tree, n, err): break match
    inc num
  if result: return true

proc check_stmt*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Asgn <local> <value>)", Asgn, match:
    if num == len or not check_local(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Store <type_id> <value> <value>)", Store, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Clear <value> <value>)", Clear, match:
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Copy <value> <value> <value>)", Copy, match:
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Call <proc> <value>*)", Call, match:
    if num == len or not check_proc(tree, n, err): break match
    inc num
    while num < len:
      if not check_value(tree, n, err): break
      inc num
  if result: return true
  matchTree "(Call <type_id> <value>+)", Call, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    var tmp = num
    while num < len:
      if not check_value(tree, n, err): break
      inc num
    if tmp == num: break match
  if result: return true
  matchTree "(Drop <value>)", Drop, match:
    if num == len or not check_value(tree, n, err): break match
    inc num
  if result: return true

proc check_continuation*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Continuation (Params) <int> <stmt>* <exit>)", Continuation, match:
    matchTree "(Params)", Params, match:
      discard
    if num == len or not result: break match
    inc num
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
    while num < len:
      if not check_stmt(tree, n, err): break
      inc num
    if num == len or not check_exit(tree, n, err): break match
    inc num
  if result: return true
  matchTree "(Continuation (Params ...))", Continuation, match:
    matchTree "(Params <type_id>?)", Params, match:
      if num < len and check_type_id(tree, n, err): inc num
    if num == len or not result: break match
    inc num
  if result: return true
  matchTree "(Except <local> <int> <stmt>* <exit>)", Except, match:
    if num == len or not check_local(tree, n, err): break match
    inc num
    if num == len or not matchAtom(tree, n, Immediate): break match
    inc num
    while num < len:
      if not check_stmt(tree, n, err): break
      inc num
    if num == len or not check_exit(tree, n, err): break match
    inc num
  if result: return true

proc check_procdef*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(ProcDef <type_id> (Locals ...) (Continuations ...))", ProcDef, match:
    if num == len or not check_type_id(tree, n, err): break match
    inc num
    matchTree "(Locals <type_id>*)", Locals, match:
      while num < len:
        if not check_type_id(tree, n, err): break
        inc num
    if num == len or not result: break match
    inc num
    matchTree "(Continuations <continuation>+)", Continuations, match:
      var tmp = num
      while num < len:
        if not check_continuation(tree, n, err): break
        inc num
      if tmp == num: break match
    if num == len or not result: break match
    inc num
  if result: return true

proc check_globaldef*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  if check_intval(tree, n, err): return true
  if check_floatval(tree, n, err): return true

proc check_module*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  matchTree "(Module (TypeDefs ...) (GlobalDefs ...) (ProcDefs ...))", Module, match:
    matchTree "(TypeDefs <type>*)", TypeDefs, match:
      while num < len:
        if not check_type(tree, n, err): break
        inc num
    if num == len or not result: break match
    inc num
    matchTree "(GlobalDefs <globaldef>*)", GlobalDefs, match:
      while num < len:
        if not check_globaldef(tree, n, err): break
        inc num
    if num == len or not result: break match
    inc num
    matchTree "(ProcDefs <procdef>*)", ProcDefs, match:
      while num < len:
        if not check_procdef(tree, n, err): break
        inc num
    if num == len or not result: break match
    inc num
  if result: return true

proc check_top*(tree: Tree, n: var NodeIndex, err: var Error): bool =
  if check_module(tree, n, err): return true


template check*(tree: Tree; n: NodeIndex; name, onErr: untyped) =
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
