open Ast
open TAst

(** This type encapsulate all the informations needed to resolve an instance,
    later in the computation. We first need to accumulate the constraints on
    the type variables. *)
type instance_to_resolve =
  { gamma: local_env (* The context in which we need to resolve it *)
  ; i: instance (* The instance to resolve *)
  ; expr: expr (* The expression that lead to this resolution *) }

(** [instance2resolve lenv sigma decl expr] computes the list of instances to
    resolve in order to call the function [decl] in the local environment [lenv].
    [sigma] is the permutation computed from the unification of the types and
    [expr] is the location that lead to the resolution. *)
let instance2resolve lenv sigma decl expr =
  List.map
    (fun inst ->
      { gamma= lenv
      ; i=
          { inst_class= inst.inst_class
          ; inst_args= List.map (subst sigma) inst.inst_args }
      ; expr } )
    decl.fun_insts

exception UnresolvedInstance of instance * instance list

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

(** [resolve_i2r] tries to resolve the "instance to resolve" in the global
    environment [genv] *)
let resolve_i2r genv i2r =
  let rec resinst lenv to_res =
    (* We check if [inst] is in the local env *)
    match
      List.find_opt
        (fun inst ->
          if
            inst.inst_class = to_res.inst_class
            && List.for_all2 can_unify
                 (List.map copy to_res.inst_args)
                 inst.inst_args
          then (* We found a matching instance in the function arguments *)
            true
          else false )
        lenv.instances
    with
    | Some _ ->
        () (* It is resolved *)
    | None -> (
        (* Otherwise, we have to find an instance or a schema to resolve it in
           the global env. To do so, we first sanitize our type variables. *)
        let typ_list_bis = sanitize to_res.inst_args in
        match TypeClass.Map.find_opt to_res.inst_class genv.schemas with
        | Some l -> (
          (* [l] is the list of schema for the class [cls_name] *)
          match
            List.find_opt
              (fun (sdecl : schema) ->
                (* We replace all variables occurring in the type of the instance *)
                let sigma = sfresh_subst sdecl.schema_tvars in
                let instvars =
                  List.map (subst sigma) sdecl.schema_prod.inst_args
                in
                if List.for_all2 can_unify typ_list_bis instvars then (
                  List.iter2 unify to_res.inst_args instvars ;
                  (* We apply the substitution for the required instances *)
                  let req_inst =
                    List.map
                      (fun req_inst ->
                        { req_inst with
                          inst_args= List.map (subst sigma) req_inst.inst_args
                        } )
                      sdecl.schema_req
                  in
                  try
                    (* we try to resolve the required instances *)
                    List.iter (resinst lenv) req_inst ;
                    true
                  with UnresolvedInstance (i, acc) ->
                    raise (UnresolvedInstance (i, sdecl.schema_prod :: acc)) )
                else false )
              l
          with
          | Some _ ->
              ()
          | None ->
              raise (UnresolvedInstance (to_res, [])) )
        | None ->
            raise (UnresolvedInstance (to_res, [])) )
  in
  try resinst i2r.gamma i2r.i
  with UnresolvedInstance (i, stack) ->
    TypingError.unresolved_instance i2r.gamma i stack i2r.expr
