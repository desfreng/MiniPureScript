include DefaultTypingEnv
include SympAst
include TypedAst

let subst sigma v =
  match Hashtbl.find_opt sigma v with Some v -> v | None -> Either.Left v

let mk_sexpr symp_expr_typ symp_expr = {symp_expr; symp_expr_typ}

let mk_const typ c = mk_sexpr typ (SConstant c)

let mk_var sigma typ v =
  match Hashtbl.find sigma v with
  | Either.Left v ->
      mk_sexpr typ (SVariable v)
  | Either.Right c ->
      mk_const typ c
