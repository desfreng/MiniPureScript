open TypedAst
open Ast
open DefaultTypingEnv
open CommonTyping
open PatternTyping
open ResolveInstance

(** Wrapped unify functions for error management. *)
let expr_unify_wrapped lenv t1 t2 expr =
  try unify t1 t2
  with UnificationError e -> TypingError.unification_error lenv e t1 t2 expr

(** [make_expr e t] creates an TAst expression from a kind and a type *)
let make_expr expr expr_typ =
  (* This expression is of type Unit, so its value can only be unit.
     Moreover, no side effect can occurs in [expr] (otherwise it
     would be an Effect Unit). So this is just the unit type ! ! *)
  if is_unit_t expr_typ then {expr= TConstant Unit; expr_typ}
  else {expr; expr_typ}

(** return the expression and its computed type with no instance to resolve. *)
let return a b = (a, b, Monoid.empty)

(** [type_expr genv lenv expr typ] checks that [expr] has type [typ] in the
    environment [lenv]. If so, returns a TAst corresponding to [expr] and the
    list of instance to resolve to performs the functions calls occurring in
    [expr]. *)
let rec type_expr genv lenv (expr : Ast.expr) typ =
  let texpr, ty, inst2res = compute_expr_type genv lenv expr in
  expr_unify_wrapped lenv ty typ expr ;
  (make_expr texpr ty, inst2res)

(** [compute_expr_type genv lenv expr] returns a TAst of the expression [expr],
    its computed type, and the list of instance to resolve to performs the
    functions calls occurring in [expr]. *)
and compute_expr_type genv lenv (expr : Ast.expr) =
  match expr.v with
  | ExprConstant cst ->
      let tconst, ty = type_constant cst in
      return (TConstant tconst) ty
  | ExprVar "_" ->
      TypingError.invalid_anonymous expr
  | ExprVar "unit" -> (
    match SMap.find_opt "unit" lenv.vartype with
    | Some (vtyp, vid) ->
        return (TVariable vid) vtyp
    | None -> (
      match Function.exists "unit" with
      | Some _ ->
          failwith "Global Constant are not yet suported"
      | None ->
          return (TConstant Unit) unit_t ) )
  | ExprVar v -> (
    match SMap.find_opt v lenv.vartype with
    | Some (vtyp, vid) ->
        return (TVariable vid) vtyp
    | None -> (
      match Function.exists v with
      | Some _ ->
          failwith "Global Constant are not yet suported"
      | None ->
          TypingError.variable_not_declared v expr ) )
  | WithType (e, t) ->
      let t_found = wf_type genv lenv t in
      let texpr, i2r = type_expr genv lenv e t_found in
      (texpr.expr, texpr.expr_typ, i2r)
  | Neg e ->
      let texpr, i2r = type_expr genv lenv e int_t in
      (TNeg texpr, int_t, i2r)
  | BinOp (lhs, ((Plus | Minus | Div | Mul) as op), rhs) ->
      (* Arithmetic operation *)
      let lhs_texpr, lhs_i2r = type_expr genv lenv lhs int_t in
      let rhs_texpr, rhs_i2r = type_expr genv lenv rhs int_t in
      (TBinOp (lhs_texpr, op, rhs_texpr), int_t, Monoid.(lhs_i2r <> rhs_i2r))
  | BinOp (lhs, ((Gt | Ge | Lt | Le) as op), rhs) ->
      (* Comparaisons *)
      let lhs_texpr, lhs_i2r = type_expr genv lenv lhs int_t in
      let rhs_texpr, rhs_i2r = type_expr genv lenv rhs int_t in
      (TBinOp (lhs_texpr, op, rhs_texpr), bool_t, Monoid.(lhs_i2r <> rhs_i2r))
  | BinOp (lhs, ((Eq | Neq) as op), rhs) ->
      (* Equality *)
      let lhs_texpr_k, lhs_t, lhs_i2r = compute_expr_type genv lenv lhs in
      let rhs_texpr_k, rhs_t, rhs_i2r = compute_expr_type genv lenv rhs in
      expr_unify_wrapped lenv lhs_t rhs_t expr ;
      if is_bool_t lhs_t || is_int_t lhs_t || is_string_t lhs_t then
        let lhs = make_expr lhs_texpr_k lhs_t in
        let rhs = make_expr rhs_texpr_k rhs_t in
        (TBinOp (lhs, op, rhs), bool_t, Monoid.(lhs_i2r <> rhs_i2r))
      else if is_unit_t lhs_t then
        (* a == b with a::Unit and b::Unit is always true. Moreover,
           because a and b cannot do side effect, we dont have to evaluate them.
           We apply the same trick for a /= b with a::Unit and b::Unit. *)
        match op with
        | Eq ->
            (TConstant (Bool true), bool_t, Monoid.(lhs_i2r <> rhs_i2r))
        | Neq ->
            (TConstant (Bool false), bool_t, Monoid.(lhs_i2r <> rhs_i2r))
        | _ ->
            assert false
      else
        TypingError.expected_type_in lenv lhs_t
          [unit_t; bool_t; int_t; string_t]
          expr
  | BinOp (lhs, ((And | Or) as op), rhs) ->
      (* Boolean operations *)
      let lhs_texpr, lhs_i2r = type_expr genv lenv lhs bool_t in
      let rhs_texpr, rhs_i2r = type_expr genv lenv rhs bool_t in
      (TBinOp (lhs_texpr, op, rhs_texpr), bool_t, Monoid.(lhs_i2r <> rhs_i2r))
  | BinOp (lhs, Concat, rhs) ->
      (* Concatenation *)
      let lhs_texpr, lhs_i2r = type_expr genv lenv lhs string_t in
      let rhs_texpr, rhs_i2r = type_expr genv lenv rhs string_t in
      ( TBinOp (lhs_texpr, Concat, rhs_texpr)
      , string_t
      , Monoid.(lhs_i2r <> rhs_i2r) )
  | If (c, tb, fb) ->
      let cond_expr, cond_i2r = type_expr genv lenv c bool_t in
      let tb_texpr_k, tb_t, tb_i2r = compute_expr_type genv lenv tb in
      let fb_texpr_k, fb_t, fb_i2r = compute_expr_type genv lenv fb in
      expr_unify_wrapped lenv tb_t fb_t expr ;
      let tb = make_expr tb_texpr_k tb_t in
      let fb = make_expr fb_texpr_k fb_t in
      (TIf (cond_expr, tb, fb), tb_t, Monoid.(cond_i2r <> tb_i2r <> fb_i2r))
  | Block l ->
      let res = List.map (fun x -> type_expr genv lenv x (effect_t unit_t)) l in
      let l_texpr = List.map fst res in
      let i2r =
        List.fold_left
          (fun acc (_, i2r) -> Monoid.(acc <> i2r))
          Monoid.empty res
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
            let v_id = Variable.fresh v_name in
            (* 3. Add the mapping v_name -> (v_typ, v_id) to the environment *)
            let lenv = add_vartype_to_lenv lenv v_name v_typ v_id in
            (* 4. Add (v_id, v_texpr) to the bindings list and, update the accumulator *)
            ((v_id, make_expr v_texp_k v_typ) :: bd, lenv, Monoid.(i2r <> v_i2r))
            )
          ([], lenv, Monoid.empty) l
      in
      (* [expr_k] is the [texpr_kind] of [e] and [te] its type *)
      let expr_k, te, e_i2r = compute_expr_type genv lenv e in
      (* For each bindings, we add a TLet struct.
         This struct is like in OCaml, we bind one variable to an expression
         and continue the computation on another one. *)
      let lexprs =
        List.fold_left
          (* fold_left because bindings is in reversed order. *)
            (fun acc (v_id, v_texpr) -> make_expr (TLet (v_id, v_texpr, acc)) te
            )
          (make_expr expr_k te) bindings
      in
      (lexprs.expr, lexprs.expr_typ, Monoid.(i2r <> e_i2r))
  | AppConstr (cst, args) -> (
    match Constructor.exists cst with
    (* [decl] is the symbol declaration associated to the constructor [cst] *)
    | Some (cid, sid) ->
        let decl = Symbol.Map.find sid genv.symbols in
        let found_ar = List.length args in
        let ((constr_args, constr_arity) as cdecl) =
          Constructor.Map.find cid decl.symbol_constr
        in
        if constr_arity <> found_ar then
          (* Not the right amount of argument to build this type *)
          TypingError.constr_arity_mismatch cid cdecl found_ar expr
        else
          (* sigma is a substitution of variable used of the type to fresh one. *)
          let sigma = lfresh_subst decl.symbol_tvars in
          (* We compute the type of all the arguments *)
          let t_args =
            List.map
              (fun x ->
                let e, t, i2r = compute_expr_type genv lenv x in
                (x, e, t, i2r) )
              args
          in
          (* We substitute all variables of [constr_args] with new one,
             waiting to be unified.
             Invariant: No type variable of [constr_args] are in [lenv.tvars] *)
          let constr_args =
            (* [args_typ] is the list of type of the constructor, with all the
               variables in [decl.vars]. *)
            let args_typ = constr_args in
            (* So, after the substitution, no variable are in [decl.vars]. *)
            List.map (subst sigma) args_typ
          in
          (* For each argument of the constructor, we unify its expected type
             (ie. [fun_args]) with the type found (ie. [t_args]). *)
          List.iter2
            (fun cst_t (arg_exp, _, arg_t, _) ->
              expr_unify_wrapped lenv cst_t arg_t arg_exp )
            constr_args t_args ;
          (* We convert the tuple (kind, typ) to an expression *)
          let args_exprs =
            List.map (fun (_, kind, typ, _) -> make_expr kind typ) t_args
          in
          (* We propagates the instances to resolve. *)
          let i2r =
            List.fold_left
              (fun acc (_, _, _, i2r) -> Monoid.(acc <> i2r))
              Monoid.empty t_args
          in
          (* We apply sigma to each type of the symbol declaration to compute
             the argument of the symbol. *)
          let data_typ =
            List.map (fun x -> Hashtbl.find sigma x) decl.symbol_tvars
          in
          (* Finally, we can build the TAst and the type ! *)
          let e = TConstructor (cid, args_exprs) in
          let t = TSymbol (sid, data_typ) in
          (e, t, i2r)
    | None ->
        TypingError.unknown_constructor cst expr )
  | AppFun (fn, args) when SMap.mem fn lenv.vartype ->
      let t, _ = SMap.find fn lenv.vartype in
      (* args <> [] and the type of our variable cannot be a function (not
         supported for now), so error ! *)
      TypingError.variable_not_a_function lenv fn t (List.length args) expr
  | AppFun (fn, args) -> (
    match Function.exists fn with
    | Some fid ->
        type_fun_call genv lenv (fid, args) expr
    | None ->
        TypingError.unknown_function fn expr )
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
            let lenv = {lenv with vartype= pat_var_env} in
            let ei_expr, ei_typ, ei_i2r = compute_expr_type genv lenv e in
            expr_unify_wrapped lenv case_t ei_typ e ;
            (make_expr ei_expr ei_typ, ei_i2r) )
          p pat_vars
      in
      (* Now, [cast_t] is the unified type of all branches of the case
         expression. We need to compute all the instances to resolve to performs
         the evaluation of each branch safely *)
      let case_i2r =
        List.fold_left
          (fun acc (_, i2r) -> Monoid.(acc <> i2r))
          Monoid.empty exprs
      in
      let e = make_expr e_texpt e_t in
      let case_texpr =
        CompileCase.compile_case genv case_t e (List.map fst pat_vars)
          (List.map fst exprs) expr
      in
      (case_texpr.expr, case_t, Monoid.(e_i2r <> case_i2r))

(** Checks that the function call made with [fid, args] is correct and well-typed. *)
and check_fun_call genv lenv (fid, args) (tvars, dargs, darity, dret) expr =
  let found_ar = List.length args in
  if darity <> found_ar then
    (* Not the right amount of argument to call the function *)
    TypingError.function_arity_mismatch fid darity found_ar expr
  else
    (* We create [sigma] in a similar way to the case of the constructor *)
    let sigma = sfresh_subst tvars in
    (* We compute the type of all the arguments *)
    let t_args =
      List.map
        (fun x ->
          let e, t, i2r = compute_expr_type genv lenv x in
          (x, e, t, i2r) )
        args
    in
    (* We substitute all variables of [decl.args] with new one,
       waiting to be unified.
       Invariant: No type variable of [fun_args] are in [lenv.tvars] *)
    let fun_args =
      (* So, after the substitution, no variable are in [decl.vars]. *)
      List.map (subst sigma) dargs
    in
    (* For each argument of the function, we unify its expected type
       (ie. [fun_args]) with the type found (ie. [t_args]). *)
    List.iter2
      (fun cst_t (arg_exp, _, arg_t, _) ->
        expr_unify_wrapped lenv cst_t arg_t arg_exp )
      fun_args t_args ;
    (* We convert each tuple (kind, typ) to an expression *)
    let args_exprs =
      List.map (fun (_, kind, typ, _) -> make_expr kind typ) t_args
    in
    (* We propagate the instance to resolve coming from the arguments. *)
    let args_i2r =
      List.fold_left
        (fun acc (_, _, _, i2r) -> Monoid.(acc <> i2r))
        Monoid.empty t_args
    in
    let res_typ = unfold (subst sigma dret) in
    (sigma, args_exprs, res_typ, args_i2r)

and type_fun_call genv lenv (fid, args) expr =
  match Function.Map.find fid genv.funs with
  | Either.Left decl ->
      (* A regular function is called *)
      let fun_decl =
        (decl.fun_tvars, decl.fun_args, decl.fun_arity, decl.fun_ret)
      in
      (* We compute the expression of each argument, the return type and all
         the instances to resolve in the arguments.
         We also returns the substitution from the quantified type of the
         function to thoses of the arguments. *)
      let sigma, args_exprs, res_typ, args_i2r =
        check_fun_call genv lenv (fid, args) fun_decl expr
      in
      (* We compute all the instances needed by the function call *)
      let arg_insts =
        List.map
          (fun (inst_class, inst_args) ->
            let inst_args = List.map (subst sigma) inst_args in
            resolve genv lenv (inst_class, inst_args) expr )
          decl.fun_insts
      in
      (TRegularFunApp (fid, arg_insts, args_exprs), res_typ, args_i2r)
  | Either.Right cid ->
      (* A function defined in a type class is called. *)
      let decl = TypeClass.Map.find cid genv.tclass in
      let fun_args, fun_arity, fun_ret =
        let tc_fdecl = Function.Map.find fid decl.tclass_decls in
        (tc_fdecl.tc_fun_args, tc_fdecl.tc_fun_arity, tc_fdecl.tc_fun_ret)
      in
      let fun_tvars = QTypeVar.Set.of_list decl.tclass_tvars in
      let fun_decl = (fun_tvars, fun_args, fun_arity, fun_ret) in
      (* We compute the expression of each argument, the return type and all
         the instances to resolve in the arguments.
         We also returns the substitution from the quantified type of the
         function to thoses of the arguments. *)
      let sigma, args_exprs, res_typ, args_i2r =
        check_fun_call genv lenv (fid, args) fun_decl expr
      in
      (* Type argument of the instance required *)
      let inst_args =
        List.map (fun qvar -> Hashtbl.find sigma qvar) decl.tclass_tvars
      in
      (* This is the instance in which this function is defineds. *)
      let fun_inst = resolve genv lenv (cid, inst_args) expr in
      ( TTypeClassFunApp (fun_inst, fid, args_exprs)
      , res_typ
      , Monoid.(args_i2r <> of_elm fun_inst) )
