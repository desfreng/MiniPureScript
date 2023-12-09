open Ast
open TAst

type instance_to_resolve = {
  gamma : local_env; (* The context in witch we need to resolve it *)
  i : instance; (* The instance to resolve *)
  expr : expr; (* The expression that lead to this resolution *)
}
(** This type encapsulate all the informations needed to resolve an instance,
    later in the computation. We first need to accumulate the constraints on
    the type variables. *)

(** [instance2resolve lenv sigma decl expr] computes the list of instances to
    resolve in order to call the function [decl] in the local environment [lenv].
    [sigma] is the permutation computed from the unification of the types and
    [expr] is the location that lead to the resolution. *)
let instance2resolve lenv sigma decl expr =
  List.map
    (fun (TInstance (cls_name, typl)) ->
      {
        gamma = lenv;
        i = TInstance (cls_name, List.map (subst sigma) typl);
        expr;
      })
    decl.finsts

exception UnresolvedInstance of instance * instance list

(** Remove non quantified variable with quantified one that are not in the
    local environment *)
let sanitize tl =
  let mapping = Hashtbl.create 17 in
  let rec loop t =
    match unfold t with
    | TVar { id; _ } -> (
        match Hashtbl.find_opt mapping id with
        | Some i -> i
        | None ->
            let vnar = TQuantifiedVar (TQVar.fresh ()) in
            Hashtbl.add mapping id vnar;
            vnar)
    | TQuantifiedVar _ as t -> t
    | TSymbol (s, args) -> TSymbol (s, List.map loop args)
  in
  List.map loop tl

(** [resolve_i2r] tries to resolve the "instance to resolve" in the global
    environment [genv] *)
let resolve_i2r genv i2r =
  let rec resinst lenv inst =
    let (TInstance (cls_name, typ_list)) = inst in
    (* We check if [inst] is in the local env *)
    match
      List.find_opt
        (fun (TInstance (inst_cls, inst_typl)) ->
          if
            inst_cls = cls_name
            && List.for_all2 can_unify (List.map copy typ_list) inst_typl
          then (* We found a matching instance in the function arguments *)
            true
          else false)
        lenv.instances
    with
    | Some _ -> () (* It is resolved *)
    | None -> (
        (* Otherwise, we have to find an instance or a schema to resolve it in
           the global env. To do so, we first sanitize our type variables. *)
        let typ_list_bis = sanitize typ_list in
        match SMap.find_opt cls_name genv.schemadecls with
        | Some l -> (
            (* [l] is the list of schema for the class [cls_name] *)
            match
              List.find_opt
                (fun (sdecl : schema_decl) ->
                  (* We replace all variables occurring in the type of the instance *)
                  let sigma = sfresh_subst sdecl.tvars in
                  let instname, instvars =
                    let (TInstance (instname, instvars)) = sdecl.prod in
                    (instname, List.map (subst sigma) instvars)
                  in
                  if List.for_all2 can_unify typ_list_bis instvars then (
                    List.iter2 unify typ_list instvars;
                    (* We apply the substitution for the required instances *)
                    let req_inst =
                      List.map
                        (fun (TInstance (cls, ttypl)) ->
                          TInstance (cls, List.map (subst sigma) ttypl))
                        sdecl.req
                    in
                    try
                      (* we try to resolve the required instances *)
                      List.iter (resinst lenv) req_inst;
                      true
                    with UnresolvedInstance (i, acc) ->
                      raise
                        (UnresolvedInstance
                           (i, TInstance (instname, instvars) :: acc)))
                  else false)
                l
            with
            | Some _ -> ()
            | None -> raise (UnresolvedInstance (inst, [])))
        | None -> raise (UnresolvedInstance (inst, [])))
  in
  try resinst i2r.gamma i2r.i
  with UnresolvedInstance (i, stack) ->
    TypingError.unresolved_instance i2r.gamma i stack i2r.expr
