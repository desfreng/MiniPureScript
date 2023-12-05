open TAst
open Ast
open CommonTyping
open PatternTyping
open ResolveInstance

(** Wrapped unify functions for error management. *)
let expr_unify_wrapped t1 t2 expr =
  try unify t1 t2
  with UnificationError e -> TypingError.unification_error e t1 t2 expr

(** [make_expr e t] creates an TAst expression from a kind and a type *)
let make_expr expr expr_typ = { expr; expr_typ }

(** [type_expr genv lenv expr typ] checks that [expr] has type [typ] in the
    environment [lenv]. If so, returns a TAst corresponding to [expr] and the
    list of instance to resolve to performs the functions calls occurring in
    [expr]. *)
let rec type_expr genv lenv (expr : Ast.expr) typ =
  let texpr, ty, inst2res = compute_expr_type genv lenv expr in
  expr_unify_wrapped ty typ expr;
  (make_expr texpr ty, inst2res)

(** [compute_expr_type genv lenv expr] returns a TAst of the expression [expr],
    its computed type, and the list of instance to resolve to performs the
    functions calls occurring in [expr]. *)
and compute_expr_type genv lenv (expr : Ast.expr) =
  match expr.v with
  | ExprConstant cst ->
      let tconst, ty = type_constant cst in
      (TConstant tconst, ty, M.empty)
  | ExprVar "_" -> TypingError.invalid_anonymous expr
  | ExprVar "unit" -> (
      match SMap.find_opt "unit" lenv.vartype with
      | Some (vtyp, vid) -> (TVariable vid, vtyp, M.empty)
      | None -> (TConstant TUnitConstant, unit_t, M.empty))
  | ExprVar v -> (
      match SMap.find_opt v lenv.vartype with
      | Some (vtyp, vid) -> (TVariable vid, vtyp, M.empty)
      | None -> TypingError.variable_not_declared v expr)
  | WithType (e, t) ->
      let t_found = wf_type genv lenv t in
      let texpr, i2r = type_expr genv lenv e t_found in
      (texpr.expr, texpr.expr_typ, i2r)
  | Neg e ->
      let texpr, i2r = type_expr genv lenv e int_t in
      let zero = { expr = TConstant (TIntConstant 0); expr_typ = int_t } in
      (TBinOp (zero, Minus, texpr), int_t, i2r)
  | BinOp (lhs, ((Plus | Minus | Div | Mul) as op), rhs) ->
      (* Arithmetic operation *)
      let lhs_texpr, lhs_i2r = type_expr genv lenv lhs int_t in
      let rhs_texpr, rhs_i2r = type_expr genv lenv rhs int_t in
      (TBinOp (lhs_texpr, op, rhs_texpr), int_t, M.(lhs_i2r <> rhs_i2r))
  | BinOp (lhs, ((Gt | Ge | Lt | Le) as op), rhs) ->
      (* Comparaisons *)
      let lhs_texpr, lhs_i2r = type_expr genv lenv lhs int_t in
      let rhs_texpr, rhs_i2r = type_expr genv lenv rhs int_t in
      (TBinOp (lhs_texpr, op, rhs_texpr), bool_t, M.(lhs_i2r <> rhs_i2r))
  | BinOp (lhs, ((Eq | Neq) as op), rhs) ->
      (* Equality *)
      let lhs_texpr_k, lhs_t, lhs_i2r = compute_expr_type genv lenv lhs in
      let rhs_texpr_k, rhs_t, rhs_i2r = compute_expr_type genv lenv rhs in
      expr_unify_wrapped lhs_t rhs_t expr;
      if
        is_unit_t lhs_t || is_bool_t lhs_t || is_int_t lhs_t
        || is_string_t lhs_t
      then
        let lhs = make_expr lhs_texpr_k lhs_t in
        let rhs = make_expr rhs_texpr_k rhs_t in
        (TBinOp (lhs, op, rhs), bool_t, M.(lhs_i2r <> rhs_i2r))
      else TypingError.expected_type_in lhs_t [ bool_t; int_t; string_t ] expr
  | BinOp (lhs, ((And | Or) as op), rhs) ->
      (* Boolean operations *)
      let lhs_texpr, lhs_i2r = type_expr genv lenv lhs bool_t in
      let rhs_texpr, rhs_i2r = type_expr genv lenv rhs bool_t in
      (TBinOp (lhs_texpr, op, rhs_texpr), bool_t, M.(lhs_i2r <> rhs_i2r))
  | BinOp (lhs, Concat, rhs) ->
      (* Concatenation *)
      let lhs_texpr, lhs_i2r = type_expr genv lenv lhs string_t in
      let rhs_texpr, rhs_i2r = type_expr genv lenv rhs string_t in
      (TBinOp (lhs_texpr, Concat, rhs_texpr), string_t, M.(lhs_i2r <> rhs_i2r))
  | If (c, tb, fb) ->
      let cond_expr, cond_i2r = type_expr genv lenv c bool_t in
      let tb_texpr_k, tb_t, tb_i2r = compute_expr_type genv lenv tb in
      let fb_texpr_k, fb_t, fb_i2r = compute_expr_type genv lenv fb in
      expr_unify_wrapped tb_t fb_t expr;
      let tb = make_expr tb_texpr_k tb_t in
      let fb = make_expr fb_texpr_k fb_t in
      (TIf (cond_expr, tb, fb), tb_t, M.(cond_i2r <> tb_i2r <> fb_i2r))
  | Block l ->
      let res = List.map (fun x -> type_expr genv lenv x (effect_t unit_t)) l in
      let l_texpr = List.map fst res in
      let i2r =
        List.fold_left (fun acc (_, i2r) -> M.(acc <> i2r)) M.empty res
      in
      (TBlock l_texpr, effect_t unit_t, i2r)
  | Let (l, e) ->
      (* bindings is a list (v_id, v_texpr) in the reversed order *)
      let bindings, lenv, i2r =
        List.fold_left
          (fun (bd, lenv, i2r) (v_name, v_exp) ->
            (* 1. Find the type of v_exp and build its texpr_kind *)
            let v_texp_k, v_typ, v_i2r = compute_expr_type genv lenv v_exp in
            (* 2. Create a new id for the variable v_name. *)
            let v_id = VarId.fresh (Some v_name) in
            (* 3. Add the mapping v_name -> (v_typ, v_id) to the environment *)
            let lenv = add_vartype_to_lenv lenv v_name v_typ v_id in
            (* 4. Add (v_id, v_texpr) to the bindings list and, update the accumulator *)
            ((v_id, make_expr v_texp_k v_typ) :: bd, lenv, M.(i2r <> v_i2r)))
          ([], lenv, M.empty) l
      in
      (* [expr_k] is the [texpr_kind] of [e] and [te] its type *)
      let expr_k, te, e_i2r = compute_expr_type genv lenv e in
      (* For each bindings, we add a TLet struct.
         This struct is like in OCaml, we bind one variable to an expression
         and continue the computation on another one.

         Small note: No need to type the continuation of the computation because
         its type is the same as the type of the let. *)
      let lexprs =
        List.fold_left
          (* fold_left because bindings is in reversed order. *)
            (fun acc (v_id, v_texpr) ->
            make_expr (TLet (v_id, v_texpr, acc)) te)
          (make_expr expr_k te) bindings
      in
      (lexprs.expr, lexprs.expr_typ, M.(i2r <> e_i2r))
  | AppConstr (cst, args) -> (
      match SMap.find_opt cst genv.constrsdecls with
      (* [decl] is the symbol declaration associated to the constructor [cst] *)
      | Some decl ->
          let found_ar = List.length args in
          let target_ar = SMap.find cst decl.constrs_arity in
          if target_ar <> found_ar then
            (* Not the right amount of argument to build this type *)
            TypingError.constr_arity_mismatch cst target_ar found_ar expr
          else
            (* sigma is a substitution of variable used of the type to fresh one. *)
            let sigma = lfresh_subst decl.tvars in
            (* We compute the type of all the arguments *)
            let t_args =
              List.map
                (fun x ->
                  let e, t, i2r = compute_expr_type genv lenv x in
                  (x, e, t, i2r))
                args
            in
            (* We substitute all variables of [constr_args] with new one,
               waiting to be unified.
               Invariant: No type variable of [constr_args] are in [lenv.tvars] *)
            let constr_args =
              (* [args_typ] is the list of type of the constructor, with all the
                 variables in [decl.vars]. *)
              let args_typ = SMap.find cst decl.constrs in
              (* So, after the substitution, no variable are in [decl.vars]. *)
              List.map (subst sigma) args_typ
            in
            (* For each argument of the constructor, we unify its expected type
               (ie. [fun_args]) with the type found (ie. [t_args]). *)
            List.iter2
              (fun cst_t (arg_exp, _, arg_t, _) ->
                expr_unify_wrapped cst_t arg_t arg_exp)
              constr_args t_args;
            (* We convert the tuple (kind, typ) to an expression *)
            let args_exprs =
              List.map (fun (_, kind, typ, _) -> make_expr kind typ) t_args
            in
            (* We propagates the instances to resolve. *)
            let i2r =
              List.fold_left
                (fun acc (_, _, _, i2r) -> M.(acc <> i2r))
                M.empty t_args
            in
            (* We apply sigma to each type of the symbol declaration to compute
               the argument of the symbol. *)
            let data_typ = List.map (fun x -> SMap.find x sigma) decl.tvars in
            (* Finally, we can build the TAst and the type ! *)
            let e = TConstructor (cst, args_exprs) in
            let t = TSymbol (decl.symbid, data_typ) in
            (e, t, i2r)
      | None -> TypingError.unknown_constructor cst expr)
  | AppFun (fn, args) when SMap.mem fn lenv.vartype ->
      let t, v_id = SMap.find fn lenv.vartype in
      if args = [] then
        (* If the function fn existed, it is masked by the variable declared.
           NB: I doubt we can enter this branch, with the current state of the
           parser... *)
        (TVariable v_id, t, M.empty)
      else
        (* args <> [] and the type of our variable cannot be a function (not
           supported for now), so error ! *)
        TypingError.variable_not_a_function fn t (List.length args) expr
  | AppFun (fn, args) -> (
      match SMap.find_opt fn genv.fundecls with
      | Some decl ->
          let found_ar = List.length args in
          if decl.arity <> found_ar then
            (* Not the right amount of argument to call the function *)
            TypingError.function_arity_mismatch fn decl.arity found_ar expr
          else
            (* We create [sigma] in a similar way to the case of the constructor *)
            let sigma = sfresh_subst decl.tvars in
            (* We compute the type of all the arguments *)
            let t_args =
              List.map
                (fun x ->
                  let e, t, i2r = compute_expr_type genv lenv x in
                  (x, e, t, i2r))
                args
            in
            (* We substitute all variables of [decl.args] with new one,
               waiting to be unified.
               Invariant: No type variable of [fun_args] are in [lenv.tvars] *)
            let fun_args =
              (* So, after the substitution, no variable are in [decl.vars]. *)
              List.map (subst sigma) decl.args
            in
            (* For each argument of the function, we unify its expected type
               (ie. [fun_args]) with the type found (ie. [t_args]). *)
            List.iter2
              (fun cst_t (arg_exp, _, arg_t, _) ->
                expr_unify_wrapped cst_t arg_t arg_exp)
              fun_args t_args;
            (* We convert each tuple (kind, typ) to an expression *)
            let args_exprs =
              List.map (fun (_, kind, typ, _) -> make_expr kind typ) t_args
            in
            (* We propagate the instance to resolve coming from the arguments. *)
            let args_i2r =
              List.fold_left
                (fun acc (_, _, _, i2r) -> M.(acc <> i2r))
                M.empty t_args
            in
            (* We compute the instances to resolve to accept the function *)
            let fun_i2r = M.from_list (instance2resolve lenv sigma decl expr) in
            let res_typ = unfold (subst sigma decl.typ) in
            (TApp (decl.fun_name, args_exprs), res_typ, M.(args_i2r <> fun_i2r))
      | None -> TypingError.unknown_function fn expr)
  | Case (e, p) ->
      (* We compute the type of e *)
      let e_texpt, e_t, e_i2r = compute_expr_type genv lenv e in
      (* We check that patterns have the same type *)
      let pat_vars =
        List.map (fun (pat, _) -> type_pattern genv lenv pat e_t) p
      in
      (* Lets compute the type of all the branches and check they have the same
         type *)
      let case_t = new_tvar () in
      let exprs =
        List.map2
          (fun (_, e) (_, pat_var_env) ->
            let lenv = { lenv with vartype = pat_var_env } in
            let ei_expr, ei_typ, ei_i2r = compute_expr_type genv lenv e in
            expr_unify_wrapped case_t ei_typ e;
            (make_expr ei_expr ei_typ, ei_i2r))
          p pat_vars
      in
      (* Now, [cast_t] is the unified type of all branches of the case
         expression. We need to compute all the instances to resolve to performs
         the evaluation of each branch safely *)
      let case_i2r =
        List.fold_left (fun acc (_, i2r) -> M.(acc <> i2r)) M.empty exprs
      in
      let e = make_expr e_texpt e_t in
      let case_texpr =
        CompileCase.compile_case genv case_t e (List.map fst pat_vars)
          (List.map fst exprs) expr
      in
      (case_texpr.expr, case_t, M.(e_i2r <> case_i2r))
