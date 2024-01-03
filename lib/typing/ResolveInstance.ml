open TAst

exception
  UnresolvedInstance of
    (TypeClass.t * ttyp list) * (TypeClass.t * ttyp list) list

exception Resolved of res_inst_kind

(** Remove non quantified variable with quantified one that are not in the
    local environment *)
let sanitize tl =
  let mapping = Hashtbl.create 17 in
  let rec loop t =
    match unfold t with
    | TVar {id; _} -> (
      match Hashtbl.find_opt mapping id with
      | Some i ->
          i
      | None ->
          let vnar = TQuantifiedVar (QTypeVar.fresh ()) in
          Hashtbl.add mapping id vnar ;
          vnar )
    | TQuantifiedVar _ as t ->
        t
    | TSymbol (s, args) ->
        TSymbol (s, List.map loop args)
  in
  List.map loop tl

let resolve_local_inst lenv (to_res_cls, to_res_args) =
  (* We check if [inst] is in the local env *)
  match TypeClass.Map.find_opt to_res_cls lenv.instances with
  | Some l -> (
    (* l is the list of all instances of typeclass [to_res_cls] in the local
       environment. *)
    try
      List.iter
        (fun (inst_arg_id, _, inst_args) ->
          if List.for_all2 can_unify (List.map copy to_res_args) inst_args then
            raise (Resolved (ArgumentInstance inst_arg_id)) )
        l ;
      None
    with Resolved r -> Some r )
  | None ->
      None

let rec resolve_global_inst genv lenv (to_res_cls, to_res_args) =
  (* We search for an instance or a schema in the global env that match
     which is compatible with the instance we need to resolve. Because we
     "leave" the local environment, we have to sanitize our type variables:
     All Weak Variables, waiting to be unified, are transformed as
     Quantified Variable. *)
  let typ_list_bis = sanitize to_res_args in
  match TypeClass.Map.find_opt to_res_cls genv.schemas with
  | Some l -> (
    (* [l] is the list of schema for the class [cls_name] *)
    try
      List.iter
        (fun sdecl ->
          (* We replace all variables occurring in the type of the instance *)
          let sigma = sfresh_subst sdecl.schema_tvars in
          let prod_class, prod_args = sdecl.schema_prod in
          let prod_args = List.map (subst sigma) prod_args in
          if List.for_all2 can_unify typ_list_bis prod_args then
            if sdecl.schema_req = [] then
              (* This is a global instance *)
              raise (Resolved (GlobalInstance sdecl.schema_id))
            else
              let req_inst =
                List.map
                  (fun (req_class, req_args) ->
                    (req_class, List.map (subst sigma) req_args) )
                  sdecl.schema_req
              in
              try
                (* we try to resolve the required instances *)
                let args = List.map (resolve_inst genv lenv) req_inst in
                raise (Resolved (GlobalSchema (sdecl.schema_id, args)))
              with UnresolvedInstance (i, acc) ->
                raise (UnresolvedInstance (i, (prod_class, prod_args) :: acc))
          )
        l ;
      None
    with Resolved r -> Some r )
  | None ->
      None

and resolve_inst genv lenv inst =
  match resolve_local_inst lenv inst with
  | Some r ->
      r
  | None -> (
    match resolve_global_inst genv lenv inst with
    | Some r ->
        r
    | None ->
        raise (UnresolvedInstance (inst, [])) )

(** [resolve_i2r] tries to resolve the "instance to resolve" in the global
    environment [genv] *)
let resolve genv lenv inst pos =
  lazy
    ( try resolve_inst genv lenv inst
      with UnresolvedInstance (i, stack) ->
        TypingError.unresolved_instance lenv i stack pos )
