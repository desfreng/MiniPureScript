open CommonSymplify

let mk_neg typ x =
  match x.symp_expr with
  | SConstant (Int i) ->
      mk_const typ (Int (-i))
  | _ ->
      mk_sexpr typ (SNeg x)

let mk_eq typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant a, SConstant b ->
      mk_const typ (Bool (a = b))
  | _ ->
      mk_sexpr typ (SCompare (lhs, Equal, rhs))

let mk_neq typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant a, SConstant b ->
      mk_const typ (Bool (a <> b))
  | _ ->
      mk_sexpr typ (SCompare (lhs, NotEqual, rhs))

let mk_gt typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Int a), SConstant (Int b) ->
      mk_const typ (Bool (a > b))
  | _ ->
      mk_sexpr typ (SCompare (lhs, Greater, rhs))

let mk_ge typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Int a), SConstant (Int b) ->
      mk_const typ (Bool (a >= b))
  | _ ->
      mk_sexpr typ (SCompare (lhs, GreaterEqual, rhs))

let mk_lt typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Int a), SConstant (Int b) ->
      mk_const typ (Bool (a < b))
  | _ ->
      mk_sexpr typ (SCompare (lhs, Lower, rhs))

let mk_le typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Int a), SConstant (Int b) ->
      mk_const typ (Bool (a <= b))
  | _ ->
      mk_sexpr typ (SCompare (lhs, LowerEqual, rhs))

let mk_add typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Int a), SConstant (Int b) ->
      mk_const typ (Int (a + b))
  | SConstant (Int 0), _ ->
      rhs
  | _, SConstant (Int 0) ->
      lhs
  | _ ->
      mk_sexpr typ (SArithOp (lhs, Add, rhs))

let mk_sub typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Int a), SConstant (Int b) ->
      mk_const typ (Int (a - b))
  | SConstant (Int 0), _ ->
      mk_neg typ rhs
  | _, SConstant (Int 0) ->
      lhs
  | _ ->
      mk_sexpr typ (SArithOp (lhs, Sub, rhs))

let mk_mul typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Int a), SConstant (Int b) ->
      mk_const typ (Int (a * b))
  | SConstant (Int 0), _ | _, SConstant (Int 0) ->
      (* The other branch cannot make any side effect because
         it's type is Int (!= Effect a). So we don't need to evaluate it. *)
      mk_const typ (Int 0)
  | SConstant (Int 1), _ ->
      rhs
  | _, SConstant (Int 1) ->
      lhs
  | _ ->
      mk_sexpr typ (SArithOp (lhs, Mul, rhs))

let mk_div typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | _, SConstant (Int 0) ->
      (* The other branch cannot make any side effect because
         it's type is Int (!= Effect a). So we don't need to evaluate it.

         In PureScript: forall x. x/0 = 0 *)
      mk_const typ (Int 0)
  | _ ->
      mk_sexpr typ (SArithOp (lhs, Div, rhs))

let mk_mod typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | _, SConstant (Int 0) | _, SConstant (Int 1) ->
      (* The other branch cannot make any side effect because
         it's type is Int (!= Effect a). So we don't need to evaluate it.

         In PureScript: forall x. x mod 0 = 0 *)
      mk_const typ (Int 0)
  | _ ->
      mk_sexpr typ (SArithOp (lhs, Mod, rhs))

let mk_str_concat typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (String a), SConstant (String b) ->
      mk_const typ (String (a ^ b))
  | SConstant (String ""), _ ->
      rhs
  | _, SConstant (String "") ->
      lhs
  | _, _ ->
      mk_sexpr typ (SStringConcat (lhs, rhs))

let mk_and typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Bool a), SConstant (Bool b) ->
      mk_const typ (Bool (a && b))
  | SConstant (Bool false), _ | _, SConstant (Bool false) ->
      (* The other branch cannot make any side effect because it's type is
         Boolean (!= Effect a). So we don't need to evaluate it. *)
      mk_const typ (Bool false)
  | SConstant (Bool true), _ ->
      rhs
  | _, SConstant (Bool true) ->
      lhs
  | _ ->
      mk_sexpr typ (SBooleanOp (lhs, And, rhs))

let mk_or typ lhs rhs =
  match (lhs.symp_expr, rhs.symp_expr) with
  | SConstant (Bool a), SConstant (Bool b) ->
      mk_const typ (Bool (a || b))
  | SConstant (Bool true), _ | _, SConstant (Bool true) ->
      (* The other branch cannot make any side effect because it's type is
         Boolean (!= Effect a). So we don't need to evaluate it. *)
      mk_const typ (Bool true)
  | SConstant (Bool false), _ ->
      rhs
  | _, SConstant (Bool false) ->
      lhs
  | _ ->
      mk_sexpr typ (SBooleanOp (lhs, Or, rhs))

let mk_not typ x =
  match x.symp_expr with
  | SConstant (Bool b) ->
      mk_const typ (Bool (not b))
  | _ ->
      mk_sexpr typ (SNot x)

let mk_if typ cond tb fb =
  match cond.symp_expr with
  | SConstant (Bool true) ->
      tb
  | SConstant (Bool false) ->
      fb
  | _ ->
      mk_sexpr typ (SIf (cond, tb, fb))
