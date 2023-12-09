open TAst
open Ast
open CommonTyping

(** Wrapped unify functions for error management. *)
let pat_unify_wrapped lenv t1 t2 pat =
  try unify t1 t2
  with UnificationError e -> TypingError.unification_error lenv e t1 t2 pat

(** [make_pat pat pat_typ] creates an TAst pattern from a kind and a type *)
let make_pat pat pat_typ = { pat; pat_typ }

(** [type_pattern genv lenv pat typ] checks that the [pat] pattern is of type
    [typ] in the [lenv] environment. If it is, it returns a pattern
    corresponding to [pat] and the variable environment in which the expressions
    filtering this pattern must be typed. *)
let rec type_pattern genv lenv (pat : Ast.pattern) typ =
  let tpat, ty, bind = compute_pattern_type lenv genv pat in
  pat_unify_wrapped lenv ty typ pat;
  ( make_pat tpat ty,
    (* If a variable is in both, we replace the existing one in [lenv] by the
       one defined in [bind] *)
    SMap.union (fun _ _ x -> Some x) lenv.vartype bind )

(** [compute_pattern_type genv expr] returns a pattern of [pat],
    its computed type, and the bindings to add to the local environment to type
    the expressions filtering this pattern. The existing bindings must be
    replaced !*)
and compute_pattern_type lenv genv (pat : Ast.pattern) =
  match pat.v with
  | PatConstant c ->
      let tconstant, ty = type_constant c in
      (TPatConstant tconstant, ty, SMap.empty)
  | PatVariable "_" ->
      (* It a wildcard, we do not add a binding in the future environment. *)
      (TPatWildcard, new_tvar (), SMap.empty)
  | PatVariable v ->
      (* This is a fresh variable, that we must introduce in the environment *)
      let v_id = VarId.fresh () in
      let v_typ = new_tvar () in
      (TPatVar v_id, v_typ, SMap.singleton v (v_typ, v_id))
  | PatConstructor (cst, args) -> (
      (* This is a filtering with a constructor. *)
      match SMap.find_opt cst genv.constrsdecls with
      | Some decl ->
          let found_ar = List.length args in
          let target_ar = SMap.find cst decl.constrs_arity in
          if target_ar <> found_ar then
            (* Not the right amount of argument to build this type *)
            TypingError.constr_arity_mismatch cst target_ar found_ar pat
          else
            (* sigma is a substitution of variable used of the type to fresh one. *)
            let sigma = lfresh_subst decl.tvars in
            (* We compute the type of all the arguments *)
            let t_args =
              List.map
                (fun x ->
                  let p, t, ev = compute_pattern_type lenv genv x in
                  (x, p, t, ev))
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
               (ie. [constr_args]) with the type found (ie. [t_args]). *)
            List.iter2
              (fun cst_t (arg_exp, _, arg_t, _) ->
                pat_unify_wrapped lenv cst_t arg_t arg_exp)
              constr_args t_args;
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
            let data_typ =
              List.map (fun x -> Hashtbl.find sigma x) decl.tvars
            in
            (* Finally, we can build the pattern and the type ! *)
            let p = TPatConstructor (cst, args_exprs) in
            let t = TSymbol (decl.symbid, data_typ) in
            (p, t, lenv)
      | None -> TypingError.unknown_constructor cst pat)
