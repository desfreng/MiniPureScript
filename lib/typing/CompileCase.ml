open TAst

type pat_matrix = {
  scrutineers : texpr list;
  pat_rows : (tpattern list * texpr) list;
}

exception NotExhaustive

(** [get_fields genv expr cst_id] returns the list of expression corresponding
    to each field of [expr] and the list of their type in the case that [expr]
    has [cst_id] as constructor. *)
let get_fields genv expr cst_id =
  match unfold expr.expr_typ with
  | TVar _ | TQuantifiedVar _ ->
      (* If it was the case, we would not be filtering by constructors *)
      assert false
  | TSymbol (sid, args) ->
      (* Declaration of the type *)
      let decl = SMap.find sid genv.symbsdecls in
      let constr_arity = SMap.find cst_id decl.constrs_arity in
      if constr_arity = 0 then ([], [])
        (* If no argument, no field to retrieve. Small optimisation to avoid
           building a substitution and applying it. *)
      else
        (* [sigma] maps the quantified variables in the symbol to those in the
           expression. *)
        let sigma =
          List.fold_left2
            (fun acc qvar typ -> SMap.add qvar typ acc)
            SMap.empty decl.tvars args
        in
        (* [cst_args] is the list of the type of each argument of the constructor *)
        let cst_args = List.map (subst sigma) (SMap.find cst_id decl.constrs) in
        (* For each field, we create the expression that retrieve its value. *)
        ( List.mapi
            (fun index t -> { expr = TGetField (expr, index); expr_typ = t })
            cst_args,
          cst_args )

(** [constructor_mat genv m pat_cstr] returns the pattern matrix of the
    constructor [pat_cstr] built from the pattern matrix [m]. *)
let constructor_mat genv m pat_cstr =
  (* [scrut] is the expression we match on (first expression of the scrutineers),
     [scrut_list] is the rest. *)
  let scrut, scrut_list =
    match m.scrutineers with
    | [] ->
        raise (Invalid_argument "The list of scrutineers must be non-empty.")
    | hd :: tl -> (hd, tl)
  in
  (* [n_scrut] is the list of scrutineers of the new matrix
     [cstr_args_typ] is the type of each argument of the constructor *)
  let n_scrut, cstr_args_typ =
    match pat_cstr with
    | TConstantConstr _ ->
        (* Constant case: the next scrutineers are the same,
           minus the first one.
           We do not have any argument, so empty type list returned. *)
        (scrut_list, [])
    | TSymbolConstr cst_id ->
        (* Constructor symbol case: the next scrutineers are :
           - The fields of the the first scrutineer
           - The rest of the scrutineers *)
        let fields, cst_typ = get_fields genv scrut cst_id in
        (fields @ scrut_list, cst_typ)
  in
  (* We build the sub matrix for this constructor *)
  let sub_mat =
    List.fold_left
      (fun m pat_row ->
        match pat_row with
        | [], _ -> assert false
        | pat :: pat_row, act -> (
            match (pat.pat, pat_cstr) with
            | TPatWildcard, _ ->
                (* We add as many wildcard as needed to the new row *)
                let new_pat_row =
                  List.map
                    (fun t -> { pat = TPatWildcard; pat_typ = t })
                    cstr_args_typ
                  @ pat_row
                in
                { m with pat_rows = (new_pat_row, act) :: m.pat_rows }
            | TPatVar v, _ ->
                (* We add as many wildcard as needed to the new row *)
                let new_pat_row =
                  List.map
                    (fun t -> { pat = TPatWildcard; pat_typ = t })
                    cstr_args_typ
                  @ pat_row
                in
                (* We bind the variable "v" to the current scrutineer in the action *)
                let new_act =
                  { expr = TLet (v, scrut, act); expr_typ = pat.pat_typ }
                in
                { m with pat_rows = (new_pat_row, new_act) :: m.pat_rows }
            | TPatConstant c, TConstantConstr c' when c = c' ->
                { m with pat_rows = (pat_row, act) :: m.pat_rows }
            | TPatConstant _, _ -> m (* not the good constant, we do nothing *)
            | TPatConstructor (cstr, patl), TSymbolConstr cid when cid = cstr ->
                (* We add the constructors pattern to the row *)
                let new_pat_row = patl @ pat_row in
                { m with pat_rows = (new_pat_row, act) :: m.pat_rows }
            | TPatConstructor _, _ ->
                m (* no the good symbol constructor, we do nothing *)))
      { scrutineers = n_scrut; pat_rows = [] }
      m.pat_rows
  in
  (* We reverse the row to keep the row order (fold_left has reversed it) *)
  { sub_mat with pat_rows = List.rev sub_mat.pat_rows }

(** [build_submat genv m] builds the sub-matrix for each constructor of the
    first column of pattern in [m] *)
let build_submat genv m =
  (* This is the set of all constructor occurring a the first pattern *)
  let cstrs_set =
    List.fold_left
      (fun acc pat_row ->
        match pat_row with
        | [], _ -> assert false
        | p :: _, _ -> (
            match p.pat with
            | TPatWildcard | TPatVar _ -> acc
            | TPatConstant cst -> CompPatConstrSet.add (TConstantConstr cst) acc
            | TPatConstructor (cst_id, _) ->
                CompPatConstrSet.add (TSymbolConstr cst_id) acc))
      CompPatConstrSet.empty m.pat_rows
  in
  (* For each constructor we build its sub-matrix. *)
  let pat_cstr_mat =
    CompPatConstrSet.fold
      (fun pat_cstr pat_cstr_mat ->
        CompPatConstrMap.add pat_cstr
          (constructor_mat genv m pat_cstr)
          pat_cstr_mat)
      cstrs_set CompPatConstrMap.empty
  in
  (* We compute the sub-matrix for the other cases. To do this, we use a
     trick: We filter with the constructor TConstConstr (TConstUnit).
     Indeed, the unit value cannot be in the pattern, see the pattern typing
     rules *)
  let other_mat = constructor_mat genv m (TConstantConstr TUnitConstant) in
  (pat_cstr_mat, other_mat)

let rec f genv typ m =
  match (m.scrutineers, m.pat_rows) with
  | _, [] -> raise NotExhaustive
  | [], (_, act) :: _ -> act
  | e :: _, _ ->
      let constr_set = pat_constr_set genv e.expr_typ in
      let constr_mat, otherwise_mat = build_submat genv m in
      let branch_expr = CompPatConstrMap.map (f genv typ) constr_mat in

      (* An otherwise branch is not mandatory when the set of
         "pattern constructors" of the type (ie. [constr_set]) is equal to the
         set of pattern constructors with a pattern matrix
         (ie. keys of [constr_mat]). *)
      if
        (not (CompPatConstrSet.is_empty constr_set))
        && CompPatConstrSet.for_all
             (fun cst -> CompPatConstrMap.mem cst constr_mat)
             constr_set
      then { expr = TContructorCase (e, branch_expr, None); expr_typ = typ }
      else
        let otherwise_expr = f genv typ otherwise_mat in
        {
          expr = TContructorCase (e, branch_expr, Some otherwise_expr);
          expr_typ = typ;
        }

(** [compile_case genv typ e pats actions] compiles the case statement over [e]
      with pattern [pats] and actions [actions] of type [typ] to an expression. *)
let compile_case genv typ e pats actions pos =
  try
    f genv typ
      {
        scrutineers = [ e ];
        pat_rows = List.map2 (fun p act -> ([ p ], act)) pats actions;
      }
  with NotExhaustive -> TypingError.not_exhaustive_case pos

(** [compile_function genv typ e pats actions] compiles the case statement over [e]
      with pattern [pats] and actions [actions] of type [typ] to an expression. *)
let compile_function genv typ scrutineers pat_rows fname decl_list =
  try f genv typ { scrutineers; pat_rows }
  with NotExhaustive -> TypingError.not_exhaustive_fun fname decl_list
