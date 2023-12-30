open TAst
open Ast
open CommonTyping
open PatternTyping
open ExpressionTyping
open ResolveInstance
open CompileCase

(** Modified version of [mapi] and [map2] of the module [List] to have both. *)
let[@tail_mod_cons] rec map2i i f l1 l2 =
  match (l1, l2) with
  | [], [] ->
      []
  | [a1], [b1] ->
      let r1 = f i a1 b1 in
      [r1]
  | a1 :: a2 :: l1, b1 :: b2 :: l2 ->
      let r1 = f i a1 b1 in
      let r2 = f (i + 1) a2 b2 in
      r1 :: r2 :: map2i (i + 2) f l1 l2
  | _, _ ->
      invalid_arg "List.map2"

let map2i f l = map2i 0 f l

let rec list_type_variables t =
  match t.v with
  | AstTVar v ->
      SSet.singleton v
  | AstTData (_, l) ->
      List.fold_left
        (fun acc x -> SSet.union (list_type_variables x) acc)
        SSet.empty l

let list_type_variables =
  List.fold_left
    (fun acc t -> SSet.union (list_type_variables t) acc)
    SSet.empty

let list_type_variables =
  List.fold_left
    (fun acc coi ->
      let (CoI_Decl (_, tl)) = coi.v in
      SSet.union (list_type_variables tl) acc )
    SSet.empty

(** [different_var_types error var_types] checks that all variables in the list
    [var_types] are distincts. If so return this list and this length. Otherwise,
    call the function [error] with the repeating variable as argument. *)
let different_var_types error var_types =
  let acc, _, arity =
    List.fold_left
      (fun (acc, var_set, arity) x ->
        let tvar = TQVar.fresh () in
        if SSet.mem x var_set then error x
        else (tvar :: acc, SSet.add x var_set, arity + 1) )
      ([], SSet.empty, 0) var_types
  in
  (acc, arity)

(** [get_function_list fname next_decls] finds all the declarations of a
    function of name [fnam] (if defined). If [fname] is [None], we returns the
    list of function declaration that matches the first one we found.

    Function declaration are returned as a tuple: function name, pattern list,
    body. We also return the following declarations. *)
let get_functions_list fname next_decls =
  (* We add each function declaration to [acc] if they have the same name as
     [fname]. *)
  let rec loop fname acc next_decls =
    match next_decls with
    | [] ->
        (acc, next_decls) (* No more declaration, we return what we have *)
    | decl :: tl -> (
      (* A declaration if found *)
      match (decl.v, fname) with
      | FunDecl (fn, pats, body), None ->
          (* No name defined, but a function declaration found. So we search
             for more function declaration of the same name as the one we
             found after saving it in [acc].*)
          loop (Some fn) ((fn, pats, body, decl) :: acc) tl
      | FunDecl (fn, pats, body), Some f_name when fn = f_name ->
          (* We found a function declaration with the name we want. So we
             search for more after saving it in [acc]. *)
          loop fname ((fn, pats, body, decl) :: acc) tl
          (* We either :
             - found a function declaration whose name is not fname
             - found another type of declaration
             In both cases -> end of the search *)
      | _ ->
          (acc, next_decls) )
  in
  let fdecls, (next_decls : decl list) = loop fname [] next_decls in
  (* We keep the order of the declaration *)
  (List.rev fdecls, next_decls)

(** [check_pats_and_expr genv lenv fdecl decl (fname, pats, expr)] checks that
    the function equation [fname] defined by the patterns [pats] and the
    expression [expr] is well-formed in the global (ie .[genv]) and local
    (ie. [lenv]) environments and matches the type declaration [fdecl] of the
    function.

    [decl] is used as a position marker. *)
let check_pats_and_expr permissive genv lenv (arity, ret_typ, args_typs)
    (fname, pats, expr, decl) =
  let case_pos = ref None in
  let new_vars = ref SMap.empty in
  (* We check that each pattern is well-formed.*)
  let nb_args = List.length pats in
  if nb_args <> arity then
    TypingError.function_arity_mismatch fname arity nb_args decl
  else
    let pats =
      (* [i] is the curent index in the list
         [lenv] the current local environment (we merge them at each iteration)
         [pat] the current pattern
         [typ] its expected type *)
      map2i
        (fun i pat typ ->
          let cpat, patenv = type_pattern genv lenv pat typ in
          ( match (cpat.pat, !case_pos) with
          | TPatVar _, _ | TPatWildcard, _ ->
              ()
          | _, None ->
              (* We have found a non variable pattern and the case position is
                 undefined, so we define it and do the same as before. *)
              case_pos := Some i
          | _, Some _ ->
              if not permissive then
                (* We have found a non variable pattern at the wrong position.  *)
                TypingError.multiples_non_var_in_fun_args fname pat ) ;
          (* we update the set of bindings *)
          new_vars :=
            SMap.union
              (fun x -> TypingError.same_variable_in_fun x fname pat)
              !new_vars patenv ;
          (* And we return the typed pattern *)
          cpat )
        pats args_typs
    in
    (* We update the local environment with the variable of the patterns *)
    let lenv = {lenv with vartype= !new_vars} in
    (* And we type the expression of the equation *)
    let texpr, i2rs = type_expr genv lenv expr ret_typ in
    (* We resolve the instances required in the function body *)
    M.fold (fun () i2r -> resolve_i2r genv i2r) () i2rs ;
    (!case_pos, (pats, texpr))

(** [check_fun_equations genv lenv fdecl fun_body] *)
let check_fun_equations genv lenv (fun_name, arity, ret_typ, args_typ) fun_body
    permissive associed_instance =
  (* We type all equations and verify that they are well-formed. *)
  let fun_data =
    List.map
      (check_pats_and_expr permissive genv lenv (arity, ret_typ, args_typ))
      fun_body
  in
  (* Were should be the pattern in the function *)
  let _ =
    match (fun_data, fun_body) with
    | [(None, _)], [_] ->
        ()
    | (None, _) :: _, (_, _, _, decl) :: _ ->
        if arity = 0 then TypingError.multiple_const_def fun_name decl
    | (Some pat_pos, _) :: _, _ ->
        (* We check that only one non variable pattern occur, at the same
           position for each equation *)
        ignore
          (List.iter2
             (fun (fpos, _) (_, _, _, decl) ->
               match fpos with
               | Some i when i = pat_pos ->
                   () (* Non var at the same position. *)
               | None ->
                   () (* Always vars *)
               | Some _ ->
                   if permissive then ()
                   else
                     (* Both Non var not at the same position *)
                     TypingError.strange_non_var_in_decls fun_name decl )
             fun_data fun_body )
    | _ ->
        assert false
  in
  (* Everything is ok. So now, we compile our function to an unique
     expression *)
  let fvars = List.init arity (fun _ -> VarId.fresh ()) in
  let fargs =
    List.map2 (fun typ varid -> make_expr (TVariable varid) typ) args_typ fvars
  in
  let decl_list = List.map (fun (_, _, _, x) -> x) fun_body in
  (* We build the pattern matrix*)
  let mat_pat = List.map snd fun_data in
  (* And compile it to an expression *)
  let fun_expr =
    compile_function genv ret_typ fargs mat_pat fun_name decl_list
  in
  (* We build the fimpl structure *)
  {fun_name; fvars; farity= arity; fun_expr; associed_instance}

(** [check_symbol genv symbol_name var_types constrs pos] checks that the symbol
    declaration of [symbol_name] with type argument [var_types] and constructors
    [constrs] is well-formed. If so, modifications are done to the global
    environment [genv]. Otherwise an error is raise at the position of the
    declaration [pos]. *)
let check_symbol genv symbol_name var_types constrs pos =
  if SMap.mem symbol_name genv.symbsdecls then
    TypingError.symbol_already_exists symbol_name pos
  else
    (* [var_list] is the list of type variable of the symbol [symbol_name] *)
    let tvars, arity =
      different_var_types
        (fun x -> TypingError.typ_var_already_decl_in_symb x symbol_name pos)
        var_types
    in
    (* We contruct the symbol declaration *)
    let symdecl =
      { symbid= symbol_name
      ; constrs= SMap.empty
      ; constrs_arity= SMap.empty
      ; tvars
      ; arity }
    in
    (* [lenv] is the local environment in witch the type of the constructor must
       be well-formed.*)
    let lenv =
      { default_lenv with
        tvars=
          List.fold_left2
            (fun acc tqvar name -> SMap.add name tqvar acc)
            SMap.empty tvars var_types }
    in
    (* We predefined the current symbol in the global environment to allow
       recursive definition. *)
    let genv =
      {genv with symbsdecls= SMap.add symbol_name symdecl genv.symbsdecls}
    in
    (* We map each constructor name to the list of its argument type [constrs]
       and arity [constrs_arity] *)
    let constrs, constrs_arity =
      List.fold_left
        (fun (constrs, constrs_arity) (constr_name, args_typs) ->
          if SMap.mem constr_name constrs then
            TypingError.constr_already_in_symb constr_name symbol_name pos
          else
            let constr_arity, args_ttyp =
              List.fold_left_map
                (fun i t -> (i + 1, wf_type genv lenv t))
                0 args_typs
            in
            ( SMap.add constr_name args_ttyp constrs
            , SMap.add constr_name constr_arity constrs_arity ) )
        (SMap.empty, SMap.empty) constrs
    in
    (* We update the symbol declaration accordingly *)
    let symdecl = {symdecl with constrs; constrs_arity} in
    (* And update it in the global environment *)
    let genv =
      {genv with symbsdecls= SMap.add symbol_name symdecl genv.symbsdecls}
    in
    (* For each constructor, we add the binding "constr_name -> symbol_decl" to
       the global environment *)
    SMap.fold
      (fun constr_name _ genv ->
        match SMap.find_opt constr_name genv.constrsdecls with
        | None ->
            (* Does not exist in genv, so we add it. *)
            { genv with
              constrsdecls= SMap.add constr_name symdecl genv.constrsdecls }
        | Some decl ->
            (* This constructor already exist ! Error. *)
            TypingError.constr_already_in_genv constr_name decl pos )
      constrs_arity genv

(** [check_type_decl genv lenv fun_name args_types res_typ] checks that the
    type declaration of the function [fun_name] with argument types [args_types]
    and return type [res_typ] is well formed in global (ie. [genv]) and local
    (ie. [lenv]) environment. If so, return a sparse function declaration.


    Spare: we do not fill the field of the instances and the
    types variables *)
let check_type_decl genv lenv fun_name args_types res_typ =
  let arity, t_args =
    List.fold_left_map (fun i t -> (i + 1, wf_type genv lenv t)) 0 args_types
  in
  let t_ret = wf_type genv lenv res_typ in
  {fun_name; tvars= TQVar.Set.empty; finsts= []; args= t_args; arity; typ= t_ret}

(** [check_class genv class_name var_types fun_decls pos] checks that the
    declaration of the class [class_name] with type variable [var_types] and
    function [fun_decls] is well formed. If so, the function declared in the
    class are added to the global environment [genv]. Otherwise, an error is
    raised at position [pos] (or more precise if possible) *)
let check_class genv class_name var_types fun_decls pos =
  if SMap.mem class_name genv.classdecls then
    TypingError.class_already_exists class_name pos
  else
    let tvars, carity =
      different_var_types
        (fun v -> TypingError.typ_var_already_decl_in_class v class_name pos)
        var_types
    in
    let tvarsmap =
      List.fold_left2
        (fun acc tqvar name -> SMap.add name tqvar acc)
        SMap.empty tvars var_types
    in
    (* We build a local environment with the type variable we checked. It will
       be used to check functions declarations. *)
    let lenv = {default_lenv with tvars= tvarsmap} in
    (* For each function of in the [fun_decls] list *)
    let cfun_decls =
      List.fold_left
        (fun fdecls f_decl ->
          match f_decl.v with
          | TypeDecl (fname, qvars, instl, args, ret) ->
              (* We check that it's well formed *)
              if SMap.mem fname fdecls then
                TypingError.same_fun_in_class fname class_name pos
              else if qvars <> [] then
                TypingError.no_qvar_in_class_fun_decl fname class_name f_decl
              else if instl <> [] then
                TypingError.no_instl_in_class_fun_decl fname class_name f_decl
              else
                (* [check_type_decl] returns the fun_decl of the function without
                   the fields of the instances and the types variables. *)
                let fdecl = check_type_decl genv lenv fname args ret in
                SMap.add fname fdecl fdecls
          | _ ->
              (* We cannot have anything else than a TypeDecl thanks to the parser. *)
              assert false )
        SMap.empty fun_decls
    in
    (* We build the class declaration *)
    let cls_decl = {class_name; carity; cfun_decls; tvars} in
    (* And add it the the environment *)
    let genv =
      {genv with classdecls= SMap.add class_name cls_decl genv.classdecls}
    in
    (* Next, we add each declared function to the global environment *)
    SMap.fold
      (fun fname fdecl genv ->
        if SMap.mem fname genv.fundecls then
          TypingError.function_already_exists fname pos
        else
          let fdecl =
            { fdecl with
              tvars= TQVar.Set.of_list tvars
            ; finsts=
                [ TInstance
                    (class_name, List.map (fun x -> TQuantifiedVar x) tvars) ]
            }
          in
          (* No error happened, so the function declaration is added to the
             global environment. *)
          {genv with fundecls= SMap.add fname fdecl genv.fundecls} )
      cfun_decls genv

let check_wf_instance genv lenv inst =
  let (CoI_Decl (c_name, inst_args)) = inst.v in
  match SMap.find_opt c_name genv.classdecls with
  | Some decl ->
      let arity, t_args =
        List.fold_left_map (fun i t -> (i + 1, wf_type genv lenv t)) 0 inst_args
      in
      if arity <> decl.carity then
        TypingError.class_arity_mismatch decl arity inst
      else TInstance (c_name, t_args)
  | None ->
      TypingError.unknown_class c_name inst

let check_instance genv tprog req_inst prod_inst fun_decls permissive decl =
  (* We compute the types variables *)
  let tvars = list_type_variables (prod_inst :: req_inst) in
  let tvars_map, tvars_set =
    SSet.fold
      (fun name (smap, tset) ->
        let tv_id = TQVar.fresh () in
        (SMap.add name tv_id smap, TQVar.Set.add tv_id tset) )
      tvars
      (SMap.empty, TQVar.Set.empty)
  in
  (* to create an environment *)
  let lenv = {default_lenv with tvars= tvars_map} in
  (* We check that instances required and produced are well formed *)
  let req_inst = List.map (check_wf_instance genv lenv) req_inst in
  let prod_inst = check_wf_instance genv lenv prod_inst in
  let (TInstance (prod_class_name, prod_typs)) = prod_inst in
  (* To build the schema *)
  let schem_decl = {prod= prod_inst; req= req_inst; tvars= tvars_set} in
  (* We append it to all the schema for the class *)
  let schem_decl_class =
    match SMap.find_opt prod_class_name genv.schemadecls with
    | Some l -> (
        (* Instances already defined, so we check if one of them can be unified
           with us *)
        let unified_existing_inst =
          List.find_opt
            (fun (sdecl : schema_decl) ->
              (* Replace all quantified var of [sdecl.prod] by weak vars *)
              let instvars =
                let sigma = sfresh_subst sdecl.tvars in
                let (TInstance (_, instvars)) = sdecl.prod in
                List.map (subst sigma) instvars
              in
              (* same for [prod_typs] *)
              let prod_typs =
                let sigma = sfresh_subst tvars_set in
                List.map (subst sigma) prod_typs
              in
              (* And test if we can unify them. *)
              List.for_all2 can_unify instvars prod_typs )
            l
        in
        match unified_existing_inst with
        | Some sdecl ->
            (* If so, report the error *)
            TypingError.can_unify_instances lenv prod_inst sdecl decl
        | None ->
            schem_decl :: l )
    | None ->
        [schem_decl]
  in
  (* And modify the global environment *)
  let genv =
    { genv with
      schemadecls= SMap.add prod_class_name schem_decl_class genv.schemadecls }
  in
  (* This is the class declaration we implement *)
  let class_decl = SMap.find prod_class_name genv.classdecls in
  (* sigma in the substitution from each argument of the class α
     to each type arguement of our instance τ *)
  let sigma =
    let sigma = lfresh_subst class_decl.tvars in
    List.iter2
      (fun var typ -> unify (Hashtbl.find sigma var) typ)
      class_decl.tvars prod_typs ;
    sigma
  in
  (* This is the environment in witch we have to check the functions in [fun_decls] *)
  let lenv = {tvars= tvars_map; instances= req_inst; vartype= SMap.empty} in
  let rec loop fdone tprog next_decls =
    if next_decls = [] then (tprog, fdone)
    else
      let fun_body, next_decls = get_functions_list None next_decls in
      let fname = List.hd fun_body |> fun (x, _, _, _) -> x in
      if SSet.mem fname fdone then
        TypingError.function_already_def_in_inst lenv fname prod_inst decl
      else
        match SMap.find_opt fname class_decl.cfun_decls with
        | Some fdecl ->
            let ret_typ = subst sigma fdecl.typ in
            let args_typ = List.map (subst sigma) fdecl.args in
            let fimpl =
              check_fun_equations genv lenv
                (fname, fdecl.arity, ret_typ, args_typ)
                fun_body permissive (Some prod_inst)
            in
            let fun_impl_list =
              match SMap.find_opt fname tprog with
              | None ->
                  [fimpl]
              | Some l ->
                  fimpl :: l
            in
            (* and add it to the program *)
            let tprog = SMap.add fname fun_impl_list tprog in
            loop (SSet.add fname fdone) tprog next_decls
        | None ->
            TypingError.function_not_in_class fname class_decl decl
  in
  let tprog, fdone = loop SSet.empty tprog fun_decls in
  if SMap.for_all (fun x _ -> SSet.mem x fdone) class_decl.cfun_decls then
    (genv, tprog)
  else TypingError.missing_functions lenv prod_inst fdone class_decl decl

let rec check_prog permissive genv tprog (p : Ast.program) :
    global_env * tprogram =
  match p with
  | [] ->
      (genv, tprog)
  | decl :: tl -> (
    match decl.v with
    | Data (dname, typ_vars, cstrs) ->
        let genv = check_symbol genv dname typ_vars cstrs decl in
        check_prog permissive genv tprog tl
    | Class (cname, typ_args, fundecls) ->
        let genv = check_class genv cname typ_args fundecls decl in
        check_prog permissive genv tprog tl
    | FunDecl (fname, _, _) ->
        TypingError.missing_fun_type_decl fname decl
    | TypeDecl _ ->
        check_fun_decl genv tprog decl tl permissive
    | Instance ((req_inst, prod_int), funimpls) ->
        let genv, tprog =
          check_instance genv tprog req_inst prod_int funimpls permissive decl
        in
        check_prog permissive genv tprog tl )

and check_fun_decl genv tprog decl next_decls permissive =
  match decl.v with
  | TypeDecl (fun_name, qvars, instl, args, ret) ->
      if SMap.mem fun_name genv.fundecls then
        TypingError.function_already_exists fun_name decl
      else
        (* We compute the list of type variable *)
        let tvars, _ =
          different_var_types
            (fun x -> TypingError.typ_var_already_decl_in_fun x fun_name decl)
            qvars
        in
        let tvarsmap =
          List.fold_left2
            (fun acc tqvar name -> SMap.add name tqvar acc)
            SMap.empty tvars qvars
        in
        (* And add them to the environment to check that instances are
           well-formed.*)
        let lenv = {tvars= tvarsmap; instances= []; vartype= SMap.empty} in
        (* We compute the list of instances of the function, to do so, we check
           that each of them is well-formed. *)
        let finsts =
          List.map
            (fun coid ->
              (* coid (class or instance decl) refers to a single instance *)
              let (CoI_Decl (cls_name, arg_typs)) = coid.v in
              match SMap.find_opt cls_name genv.classdecls with
              | Some decl ->
                  (* We found the class in the [genv]. Let's check that each
                     type of the instance is well-formed *)
                  let arity, insts =
                    List.fold_left_map
                      (fun i typ -> (i + 1, wf_type genv lenv typ))
                      0 arg_typs
                  in
                  (* Check that arity is the same *)
                  if arity <> decl.carity then
                    TypingError.class_arity_mismatch decl arity coid
                  else TInstance (cls_name, insts)
              | None ->
                  TypingError.unknown_class cls_name decl )
            instl
        in
        (* We build the function declaration structure *)
        let fdecl =
          let fdecl = check_type_decl genv lenv fun_name args ret in
          {fdecl with finsts; tvars= TQVar.Set.of_list tvars}
        in
        (* And add it to the global environment *)
        let genv =
          {genv with fundecls= SMap.add fun_name fdecl genv.fundecls}
        in
        (* We add the instances to the environment *)
        let lenv = {lenv with instances= finsts} in
        let fun_body, next_decls =
          get_functions_list (Some fun_name) next_decls
        in
        if fun_body = [] then TypingError.missing_fun_impl fun_name decl
        else
          let fimpl =
            check_fun_equations genv lenv
              (fdecl.fun_name, fdecl.arity, fdecl.typ, fdecl.args)
              fun_body permissive None
          in
          (* and add it to the program *)
          let tprog = SMap.add fun_name [fimpl] tprog in
          check_prog permissive genv tprog next_decls
  | _ ->
      assert false

let check_program permissive p =
  let genv, prog = check_prog permissive default_genv SMap.empty p in
  if SMap.mem "main" prog then (genv, prog) else TypingError.missing_main p
