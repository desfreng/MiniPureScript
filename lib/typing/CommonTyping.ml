open TAst
open DefaultTypingEnv

(** [add_vartype_to_lenv] add the binding about the variable [v_name] of type
    [v_typ] with id [v_id] to the local environment [lenv] *)
let add_vartype_to_lenv lenv v_name v_typ v_id =
  {lenv with vartype= SMap.add v_name (v_typ, v_id) lenv.vartype}

(** [wf_type] Check if [t] is a well formed type in the environment [env]. If
    so, return its corresponding type. Otherwise, raise a [TypeError] with kind
    [IllFormedType] *)
let rec wf_type genv lenv (t : Ast.typ) =
  match t.v with
  | AstTVar v -> (
    match SMap.find_opt v lenv.tvars with
    | Some id ->
        TQuantifiedVar id
    | None ->
        TypingError.unknown_type_var v t )
  | AstTData (n, args) -> (
    match Symbol.exists n with
    | Some sid ->
        let decl = Symbol.Map.find sid genv.symbols in
        let a = List.length args in
        if a = decl.symbol_arity then
          let targs = List.map (wf_type genv lenv) args in
          TSymbol (sid, targs)
        else TypingError.symbol_arity_mismatch sid decl.symbol_arity a t
    | None ->
        TypingError.unknown_symbol n t )

(** [type_constant] returns a TAst of an Ast constant with its type. *)
let type_constant (cst : Ast.constant) =
  match cst.v with
  | True ->
      (Constant.TBool true, bool_t)
  | False ->
      (Constant.TBool false, bool_t)
  | Int i ->
      (Constant.TInt i, int_t)
  | Str s ->
      (Constant.TString s, string_t)
