open TAst
open Ast

(** [add_vartype_to_lenv lenv v_name v_typ v_id] add the binding about the
    variable [v_name] of type [v_typ] with id [v_id] to the local environement
    [lenv]*)
let add_vartype_to_lenv lenv v_name v_typ v_id =
  { lenv with vartype = SMap.add v_name (v_typ, v_id) lenv.vartype }

(** Wrapped unify functions for error management. *)
let expr_unify_wrapped t1 t2 expr =
  try unify t1 t2
  with UnificationError e -> TypingError.expr_unification_error e t1 t2 expr

(** Wrapped unify functions for error management. *)
let pat_unify_wrapped t1 t2 pat =
  try unify t1 t2
  with UnificationError e -> TypingError.pat_unification_error e t1 t2 pat

(** A small module to concatenate things quikly *)
module M : sig
  type 'a t

  val empty : 'a t
  val from_list : 'a list -> 'a t
  val ( <> ) : 'a t -> 'a t -> 'a t
  val fold : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
end = struct
  type 'a t = Empty | Leaf of 'a list | Concat of 'a t * 'a t

  let empty = Empty
  let from_list x = Leaf x

  let ( <> ) a b =
    match (a, b) with Empty, t | t, Empty -> t | a, b -> Concat (a, b)

  let rec fold f acc = function
    | Empty -> acc
    | Leaf x -> List.fold_left f acc x
    | Concat (a, b) -> fold f (fold f acc a) b
end

type instance_to_resolve = {
  gamma : local_env; (* The context in witch we need to resolve it *)
  i : instance; (* The instance to resolve *)
  expr : expr; (* The expression that leed to this resolution *)
}
(** This type encapsulate all the informations needed to resolve an instance,
    later in the computation. We first need to accumulate the constraints on
    the type variables. *)

(** [instance2resolve lenv sigma decl expr] computes the list of instances to
    resolve in order to call the function [decl] in the local environment [lenv].
    [sigma] is the permutation computed from the unification of the types and
    [expr] is the location that leed to the resolution. *)
let instance2resolve lenv sigma decl expr =
  List.map
    (fun (cls_name, typl) ->
      { gamma = lenv; i = (cls_name, List.map (subst sigma) typl); expr })
    decl.finsts

(** [wf_type env t] Check if [t] is a well formed type in the environement
    [env]. If so, return its corresponding type.
    Otherwise, raise a [TypeError] with kind [IllFormedType] *)
let rec wf_type genv lenv (t : Ast.typ) =
  match t.v with
  | AstTVar v ->
      if SSet.mem v lenv.tvars then TQuantifiedVar v
      else TypingError.unknown_type_var v t
  | AstTData (n, args) -> (
      match SMap.find_opt n genv.symbsdecls with
      | Some decl ->
          let a = List.length args in
          if a = decl.arity then
            let targs = List.map (wf_type genv lenv) args in
            TSymbol (decl.symbid, targs)
          else TypingError.symbol_arity_mismatch decl a t
      | None -> TypingError.unknown_symbol_type n t)

(** [compute_expr_type lenv cst] returns the type and a TAst of the constant [cst] *)
let type_const (cst : Ast.constant) =
  match cst.v with
  | True -> (TConstBool true, bool_t)
  | False -> (TConstBool false, bool_t)
  | Int i -> (TConstInt i, int_t)
  | Str s -> (TConstString s, string_t)

let make_pat pat pat_typ = { pat; pat_typ }

(** [type_pattern genv lenv pat typ] checks that the [pat] pattern is of type
    [typ] in the [lenv] environment. If it is, it returns a pattern
    corresponding to [pat] and the environment in which the expressions
    filtering this pattern must be typed. *)
let rec type_pattern genv lenv (pat : Ast.pattern) typ =
  let tpat, ty, bind = compute_pattern_type genv pat in
  pat_unify_wrapped ty typ pat;
  ( make_pat tpat ty,
    (* If a variable is in both, we replace the existing one in [lenv] by the
       one defined in [bind] *)
    { lenv with vartype = SMap.union (fun _ _ x -> Some x) lenv.vartype bind }
  )

(** [compute_pattern_type genv expr] returns a pattern of [pat],
    its computed type, and the bindings to add to the local environment to type
    the expressions filtering this pattern. The existing bindings must be
    replaced !*)
and compute_pattern_type genv (pat : Ast.pattern) =
  match pat.v with
  | PatConst c ->
      let tconst, ty = type_const c in
      (TPatConstant tconst, ty, SMap.empty)
  | PatVar "_" ->
      (* It a wildcard, we do not add a binding in the future environement. *)
      (TPatWildcard, new_tvar (), SMap.empty)
  | PatVar v ->
      (* This is a fresh variable, that we must introduce in the environement *)
      let v_id = VarId.fresh (Some v) in
      let v_typ = new_tvar () in
      (TPatVar v_id, v_typ, SMap.singleton v (v_typ, v_id))
  | PatConstructor (cst, args) -> (
      (* This is a filtering with a constructor. *)
      match SMap.find_opt cst genv.constsdecls with
      | Some (cst_id, decl) ->
          let found_ar = List.length args in
          let target_ar = ConstMap.find cst_id decl.consts_arity in
          if target_ar <> found_ar then
            (* Not the right amount of argument to build this type *)
            TypingError.pat_const_arity_mismatch cst target_ar found_ar pat
          else
            (* sigma is a substitution of variable used of the type to fresh one. *)
            let sigma = lfresh_subst decl.tvars in
            (* We compute the type of all the arguments *)
            let t_args =
              List.map
                (fun x ->
                  let p, t, ev = compute_pattern_type genv x in
                  (x, p, t, ev))
                args
            in
            (* We subtitute all variables of [const_args] with new one,
               waiting to be unified.
               Invariant: No type variable of [const_args] are in [lenv.tvars] *)
            let const_args =
              (* [args_typ] is the list of type of the constructor, with all the
                 variables in [decl.vars]. *)
              let args_typ = ConstMap.find cst_id decl.consts in
              (* So, after the substitution, no variable are in [decl.vars]. *)
              List.map (subst sigma) args_typ
            in
            (* For each argument of the constructor, we unify its expected type
               (ie. [const_args]) with the type found (ie. [t_args]). *)
            List.iter2
              (fun cst_t (arg_exp, _, arg_t, _) ->
                pat_unify_wrapped cst_t arg_t arg_exp)
              const_args t_args;
            (* We convert the tuple (kind, typ) to an expression *)
            let args_exprs =
              List.map (fun (_, kind, typ, _) -> make_pat kind typ) t_args
            in
            (* We merge the variables added to the environment. *)
            let lenv =
              List.fold_left
                (fun acc (_, _, _, ev) ->
                  SMap.union
                    (fun x _ _ -> TypingError.same_variable_in_pat x pat)
                    acc ev)
                SMap.empty t_args
            in
            (* We apply sigma to each type of the symbol declaration to compute
               the argument of the symbol. *)
            let data_typ = List.map (fun x -> SMap.find x sigma) decl.tvars in
            (* Finnally, we can build the pattern and the type ! *)
            let p = TPatConstructor (cst_id, args_exprs) in
            let t = TSymbol (decl.symbid, data_typ) in
            (p, t, lenv)
      | None -> TypingError.pat_unknown_constructor cst pat)

(** [make_expr e t] creates an TAst expression from a kind and a type *)
let make_expr expr expr_typ = { expr; expr_typ }

(** [type_expr genv lenv expr typ] checks that [expr] has type [typ] in the
    environement [lenv]. If so, returns a TAst corresponding to [expr] and the
    list of instance to resolve to performs the functions calls occuring in
    [expr]. *)
let rec type_expr genv lenv (expr : Ast.expr) typ =
  let texpr, ty, inst2res = compute_expr_type genv lenv expr in
  expr_unify_wrapped ty typ expr;
  (make_expr texpr ty, inst2res)

(** [compute_expr_type genv lenv expr] returns a TAst of the expression [expr],
    its computed type, and the list of instance to resolve to performs the
    functions calls occuring in [expr]. *)
and compute_expr_type genv lenv (expr : Ast.expr) =
  match expr.v with
  | ExprConst cst ->
      let tconst, ty = type_const cst in
      (TConstant tconst, ty, M.empty)
  | ExprVar "_" -> TypingError.invalid_anonymous expr
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
      let zero = { expr = TConstant (TConstInt 0); expr_typ = int_t } in
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
      if is_bool_t lhs_t || is_int_t lhs_t || is_string_t lhs_t then
        let lhs = make_expr lhs_texpr_k lhs_t in
        let rhs = make_expr rhs_texpr_k rhs_t in
        (TBinOp (lhs, op, rhs), lhs_t, M.(lhs_i2r <> rhs_i2r))
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
            (* 3. Add the mapping v_name -> (v_typ, v_id) to the environement *)
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
            (fun acc (v_id, v_texpr) -> TLet (v_id, v_texpr, acc))
          expr_k bindings
      in
      (lexprs, te, M.(i2r <> e_i2r))
  | AppConst (cst, args) -> (
      match SMap.find_opt cst genv.constsdecls with
      (* [decl] is the symbol declaration associed to the constructor [const_id] *)
      | Some (cst_id, decl) ->
          let found_ar = List.length args in
          let target_ar = ConstMap.find cst_id decl.consts_arity in
          if target_ar <> found_ar then
            (* Not the right amount of argument to build this type *)
            TypingError.expr_const_arity_mismatch cst target_ar found_ar expr
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
            (* We subtitute all variables of [const_args] with new one,
               waiting to be unified.
               Invariant: No type variable of [const_args] are in [lenv.tvars] *)
            let const_args =
              (* [args_typ] is the list of type of the constructor, with all the
                 variables in [decl.vars]. *)
              let args_typ = ConstMap.find cst_id decl.consts in
              (* So, after the substitution, no variable are in [decl.vars]. *)
              List.map (subst sigma) args_typ
            in
            (* For each argument of the constructor, we unify its expected type
               (ie. [fun_args]) with the type found (ie. [t_args]). *)
            List.iter2
              (fun cst_t (arg_exp, _, arg_t, _) ->
                expr_unify_wrapped cst_t arg_t arg_exp)
              const_args t_args;
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
            (* Finnally, we can build the TAst and the type ! *)
            let e = TConstructor (cst_id, args_exprs) in
            let t = TSymbol (decl.symbid, data_typ) in
            (e, t, i2r)
      | None -> TypingError.expr_unknown_constructor cst expr)
  | AppFun (fn, args) when SMap.mem fn lenv.vartype ->
      let t, v_id = SMap.find fn lenv.vartype in
      if args = [] then
        (* If the function fn existed, it is masked by the variable declared.
           NB: I doubt we can enter this branch, with the current state of the
           parser... *)
        (TVariable v_id, t, M.empty)
      else
        (* args <> [] but the type of our variable cannot be a function (not
           supported for now), so error ! *)
        TypingError.variable_not_a_function fn t (List.length args) expr
  | AppFun (fn, args) -> (
      match SMap.find_opt fn genv.fundecls with
      | Some decl ->
          let found_ar = List.length args in
          if decl.arity <> found_ar then
            (* Not the right amount of argument to call the function *)
            TypingError.function_arity_mismatch decl found_ar expr
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
            (* We subtitute all variables of [decl.args] with new one,
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
            (* We propagate the instance to resolve comming from the arguments. *)
            let args_i2r =
              List.fold_left
                (fun acc (_, _, _, i2r) -> M.(acc <> i2r))
                M.empty t_args
            in
            (* We compute the instances to resolve to accept the function *)
            let fun_i2r = M.from_list (instance2resolve lenv sigma decl expr) in
            let res_typ = unfold (subst sigma decl.typ) in
            (TApp (fn, args_exprs), res_typ, M.(args_i2r <> fun_i2r))
      | None -> TypingError.unknown_function fn expr)
  | Case (e, p) ->
      (* We compute the type of e *)
      let e_texpt, e_t, e_i2r = compute_expr_type genv lenv e in
      (* We check that paterns have the same type *)
      let pat_vars =
        List.map (fun (pat, _) -> type_pattern genv lenv pat e_t) p
      in
      (* Lets compute the type of all the branches and check they have the same
         type *)
      let case_t = new_tvar () in
      let exprs =
        List.map2
          (fun (_, e) (_, lenv) ->
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
        Temp.compile_case e (List.map fst pat_vars) (List.map fst exprs)
      in
      (case_texpr.expr, case_t, M.(e_i2r <> case_i2r))
