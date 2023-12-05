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

exception UnresolvedInstance of instance

(** Remove non quantified variable with quantified one that are not in the
    local environment *)
let sanitize tl =
  let cpt = ref 0 in
  let mapping = ref TVarMap.empty in
  let rec loop t =
    match unfold t with
    | TVar { id; _ } -> (
        match TVarMap.find_opt id !mapping with
        | Some i -> i
        | None ->
            let vnar = TQuantifiedVar ("'w" ^ string_of_int !cpt) in
            incr cpt;
            mapping := TVarMap.add id vnar !mapping;
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
           the global env *)
        match SMap.find_opt cls_name genv.schemadecls with
        | Some l -> (
            (* [l] is the list of schema for the class [cls_name] *)
            match
              List.find_opt
                (fun (sdecl : schema_decl) ->
                  (* We replace all variables occurring in the type of the instance *)
                  let sigma = sfresh_subst sdecl.tvars in
                  let insttvar =
                    let (TInstance (_, insttvar)) = sdecl.prod in
                    List.map (subst sigma) insttvar
                  in
                  let typ_list_bis = sanitize typ_list in
                  if List.for_all2 can_unify typ_list_bis insttvar then (
                    List.iter2 unify typ_list insttvar;
                    (* We apply the substitution for the required instances *)
                    let req_inst =
                      List.map
                        (fun (TInstance (cls, ttypl)) ->
                          TInstance (cls, List.map (subst sigma) ttypl))
                        sdecl.req
                    in
                    (* we try to resolve the required instances *)
                    List.iter (resinst lenv) req_inst;
                    true)
                  else false)
                l
            with
            | Some _ -> ()
            | None -> raise (UnresolvedInstance inst))
        | None -> raise (UnresolvedInstance inst))
  in
  try resinst i2r.gamma i2r.i
  with UnresolvedInstance i -> TypingError.unresolved_instance i i2r.expr
