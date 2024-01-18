open AllocAst

(** [local_inst] t compute the set of all local instances occuring in an
    instance tree. *)
let rec local_inst = function
  | TLocalInstance i ->
      Instance.Set.singleton i
  | TGlobalInstance _ ->
      Instance.Set.empty
  | TGlobalSchema (_, l, _) ->
      List.fold_left
        (fun li i -> Instance.Set.union li (local_inst i))
        Instance.Set.empty l

(** [fv_and_li e] computes the free vars occuring and the local instance
    used in [e]. *)
let rec fv_and_li e =
  match e.symp_expr with
  | SConstant _ ->
      (Variable.Set.empty, Instance.Set.empty)
  | SVariable v | SGetField (v, _) ->
      (Variable.Set.singleton v, Instance.Set.empty)
  | SNeg arg | SNot arg ->
      fv_and_li arg
  | SArithOp (lhs, _, rhs)
  | SBooleanOp (lhs, _, rhs)
  | SCompare (lhs, _, rhs)
  | SStringConcat (lhs, rhs) ->
      let lhs_fv, lhs_ui = fv_and_li lhs in
      let rhs_fv, rhs_ui = fv_and_li rhs in
      (Variable.Set.union lhs_fv rhs_fv, Instance.Set.union lhs_ui rhs_ui)
  | SFunctionCall (_, i, l) ->
      let fv, li =
        List.fold_left
          (fun (fv, li) arg ->
            let fv_arg, li_arg = fv_and_li arg in
            (Variable.Set.union fv fv_arg, Instance.Set.union li li_arg) )
          (Variable.Set.empty, Instance.Set.empty)
          l
      in
      ( fv
      , List.fold_left (fun li i -> Instance.Set.union li (local_inst i)) li i
      )
  | SInstanceCall (i, _, l) ->
      let fv, li =
        List.fold_left
          (fun (fv, li) arg ->
            let fv_arg, li_arg = fv_and_li arg in
            (Variable.Set.union fv fv_arg, Instance.Set.union li li_arg) )
          (Variable.Set.empty, Instance.Set.empty)
          l
      in
      (fv, Instance.Set.union li (local_inst i))
  | SConstructor (_, l) ->
      List.fold_left
        (fun (fv, li) arg ->
          let fv_arg, li_arg = fv_and_li arg in
          (Variable.Set.union fv fv_arg, Instance.Set.union li li_arg) )
        (Variable.Set.empty, Instance.Set.empty)
        l
  | SBlock l ->
      List.fold_left
        (fun (fv, ui) e ->
          let fv_e, ui_e = fv_and_li e in
          (Variable.Set.union fv fv_e, Instance.Set.union ui ui_e) )
        (Variable.Set.empty, Instance.Set.empty)
        l
  | SIf (a, b, c) ->
      let fv, ui = fv_and_li a in
      let fv, ui =
        let fv_b, ui_b = fv_and_li b in
        (Variable.Set.union fv fv_b, Instance.Set.union ui ui_b)
      in
      let fv, ui =
        let fv_c, ui_c = fv_and_li c in
        (Variable.Set.union fv fv_c, Instance.Set.union ui ui_c)
      in
      (fv, ui)
  | SLet (v, x, y) ->
      let fv, ui =
        let fv_y, ui_y = fv_and_li y in
        (Variable.Set.remove v fv_y, ui_y)
      in
      let fv, ui =
        let fv_x, ui_x = fv_and_li x in
        (Variable.Set.union fv fv_x, Instance.Set.union ui ui_x)
      in
      (fv, ui)
  | SIntCompareAndBranch {var; lower; equal; greater; _}
  | SStringCompareAndBranch {var; lower; equal; greater; _} ->
      let fv = Variable.Set.singleton var in
      let fv, ui =
        let fv_l, ui_l = fv_and_li lower in
        (Variable.Set.union fv fv_l, ui_l)
      in
      let fv, ui =
        let fv_e, ui_e = fv_and_li equal in
        (Variable.Set.union fv fv_e, Instance.Set.union ui ui_e)
      in
      let fv, ui =
        let fv_g, ui_g = fv_and_li greater in
        (Variable.Set.union fv fv_g, Instance.Set.union ui ui_g)
      in
      (fv, ui)
  | SContructorCase (v, _, branchs, other) ->
      let fv, ui = (Variable.Set.singleton v, Instance.Set.empty) in
      let fv, ui =
        Constructor.Map.fold
          (fun _ e (fv, ui) ->
            let fv_e, ui_e = fv_and_li e in
            (Variable.Set.union fv fv_e, Instance.Set.union ui ui_e) )
          branchs (fv, ui)
      in
      let fv, ui =
        match other with
        | None ->
            (fv, ui)
        | Some o ->
            let fv_o, ui_o = fv_and_li o in
            (Variable.Set.union fv fv_o, Instance.Set.union ui ui_o)
      in
      (fv, ui)

let fv_and_li l =
  let fv, li =
    List.fold_left
      (fun (fv, ui) e ->
        let fv_e, ui_e = fv_and_li e in
        (Variable.Set.union fv fv_e, Instance.Set.union ui ui_e) )
      (Variable.Set.empty, Instance.Set.empty)
      l
  in
  (Variable.Set.elements fv, Instance.Set.elements li)

type alloc_env =
  { word_size: int
  ; var_pos: (Variable.t, var_pos) Hashtbl.t
  ; new_local_blocks: (label, local_afun_part) Hashtbl.t
  ; inst_pos: (Instance.t, inst_pos) Hashtbl.t
  ; fid: Function.t }

let rec alloc_inst aenv = function
  | TLocalInstance i ->
      ALocalInst (Hashtbl.find aenv.inst_pos i)
  | TGlobalInstance s ->
      AGlobalInst s
  | TGlobalSchema (s, args, i) ->
      AGlobalSchema (s, List.map (alloc_inst aenv) args, i)

let mk_aexpr typ ae = {alloc_expr= ae; alloc_expr_typ= typ}

let rec allocate_expr aenv fp_cur e =
  let sexpr, typ = (e.symp_expr, e.symp_expr_typ) in
  match sexpr with
  | SConstant c ->
      (mk_aexpr typ (AConstant c), fp_cur)
  | SVariable v ->
      let v_pos = Hashtbl.find aenv.var_pos v in
      (mk_aexpr typ (AVariable v_pos), fp_cur)
  | SNeg se ->
      let ae, fp_max = allocate_expr aenv fp_cur se in
      (mk_aexpr typ (ANeg ae), fp_max)
  | SNot se ->
      let ae, fp_max = allocate_expr aenv fp_cur se in
      (mk_aexpr typ (ANot ae), fp_max)
  | SArithOp (lhs, op, rhs) ->
      let alhs, fp_max_1 = allocate_expr aenv fp_cur lhs in
      let arhs, fp_max_2 = allocate_expr aenv fp_cur rhs in
      (mk_aexpr typ (AArithOp (alhs, op, arhs)), max fp_max_1 fp_max_2)
  | SBooleanOp (lhs, op, rhs) ->
      let alhs, fp_max_1 = allocate_expr aenv fp_cur lhs in
      let arhs, fp_max_2 = allocate_expr aenv fp_cur rhs in
      (mk_aexpr typ (ABooleanOp (alhs, op, arhs)), max fp_max_1 fp_max_2)
  | SCompare (lhs, op, rhs) ->
      let alhs, fp_max_1 = allocate_expr aenv fp_cur lhs in
      let arhs, fp_max_2 = allocate_expr aenv fp_cur rhs in
      (mk_aexpr typ (ACompare (alhs, op, arhs)), max fp_max_1 fp_max_2)
  | SStringConcat (lhs, rhs) ->
      let alhs, fp_max_1 = allocate_expr aenv fp_cur lhs in
      let arhs, fp_max_2 = allocate_expr aenv fp_cur rhs in
      (mk_aexpr typ (AStringConcat (alhs, arhs)), max fp_max_1 fp_max_2)
  | SFunctionCall (fid, instl, args) ->
      let fp_max, aargs =
        List.fold_left_map
          (fun fp_max arg ->
            let aarg, fp_max_1 = allocate_expr aenv fp_cur arg in
            (max fp_max fp_max_1, aarg) )
          fp_cur args
      in
      let ainstl = List.map (alloc_inst aenv) instl in
      (mk_aexpr typ (AFunctionCall (fid, ainstl, aargs)), fp_max)
  | SInstanceCall (inst, fid, args) ->
      let fp_max, aargs =
        List.fold_left_map
          (fun fp_max arg ->
            let aarg, fp_max_1 = allocate_expr aenv fp_cur arg in
            (max fp_max fp_max_1, aarg) )
          fp_cur args
      in
      let ainst = alloc_inst aenv inst in
      (mk_aexpr typ (AInstanceCall (ainst, fid, aargs)), fp_max)
  | SConstructor (cid, args) ->
      let fp_max, aargs =
        List.fold_left_map
          (fun fp_max arg ->
            let aarg, fp_max_1 = allocate_expr aenv fp_cur arg in
            (max fp_max fp_max_1, aarg) )
          fp_cur args
      in
      (mk_aexpr typ (AConstructor (cid, aargs)), fp_max)
  | SIf (cond, tb, fb) ->
      let acond, fp_max_1 = allocate_expr aenv fp_cur cond in
      let atb, fp_max_2 = allocate_expr aenv fp_cur tb in
      let afb, fp_max_3 = allocate_expr aenv fp_cur fb in
      let fp_max = max fp_max_1 (max fp_max_2 fp_max_3) in
      (mk_aexpr typ (AIf (acond, atb, afb)), fp_max)
  | SBlock l -> (
    match l with
    | [] ->
        (* A do block cannot be empty ! *)
        assert false
    | [x] ->
        (* x is of type Effect Unit so we can just return it directly,
           no closure needed (x is already one !) and no label introduced. *)
        allocate_expr aenv fp_cur x
    | l ->
        (* We introduce a new closure with a new label. *)
        let block_lbl = local_lbl aenv.fid in
        (* We compute the free vars and the used local instances in the do
           block. *)
        let fv_list, li_list = fv_and_li l in
        (* We process the new label. To do so, we create a new environment
           with the position of each variable in the closure. *)
        let closure_aenv =
          { var_pos= Hashtbl.create 17
          ; word_size= aenv.word_size
          ; fid= aenv.fid
          ; new_local_blocks= aenv.new_local_blocks
          ; inst_pos= Hashtbl.create 17 }
        in
        let index =
          (* the ith variable of the closure is a the offset
             [(i + 1) * word_size]. Exemple :
             the first one is a 8(%...), the second 16(%...), etc.

             That's why we start index at 1. *)
          List.fold_left
            (fun index v ->
              Hashtbl.add closure_aenv.var_pos v
                (AClosVar (index * aenv.word_size)) ;
              index + 1 )
            1 fv_list
        in
        let closure_size =
          (* Local instances used in the closure are directly put after the
             variables. *)
          List.fold_left
            (fun index v ->
              Hashtbl.add closure_aenv.inst_pos v
                (AClosInst (index * aenv.word_size)) ;
              index + 1 )
            index li_list
        in
        let block_fp_max, block_exprs =
          List.fold_left_map
            (fun fp_max arg ->
              let ae, fp_max_expr = allocate_expr closure_aenv 0 arg in
              let ae = mk_aexpr typ (ADoEffect ae) in
              (max fp_max fp_max_expr, ae) )
            0 l
        in
        let new_local_block =
          {local_body= block_exprs; local_stack_reserved= block_fp_max}
        in
        Hashtbl.add aenv.new_local_blocks block_lbl new_local_block ;
        (* We compute the position of each free variable occuring in this
           closure *)
        let vars_pos =
          List.map
            (fun v ->
              match Hashtbl.find_opt aenv.var_pos v with
              | Some tmp ->
                  tmp
              | None ->
                  Format.eprintf "Not found: %a@." Variable.pp v ;
                  raise Not_found )
            fv_list
        in
        (* We do the same for the local instances used *)
        let loc_insts_pos = List.map (Hashtbl.find aenv.inst_pos) li_list in
        (* And we build it. *)
        let clos =
          mk_aexpr typ
            (ALocalClosure (block_lbl, vars_pos, loc_insts_pos, closure_size))
        in
        (clos, fp_cur) )
  | SLet (v, x, y) ->
      let x, fp_max_1 = allocate_expr aenv fp_cur x in
      let fp_cur = fp_cur + aenv.word_size in
      let v_pos = AStackVar (-fp_cur) in
      Hashtbl.add aenv.var_pos v v_pos ;
      let y, fp_max_2 = allocate_expr aenv fp_cur y in
      (mk_aexpr typ (ALet (-fp_cur, x, y)), max fp_max_1 fp_max_2)
  | SIntCompareAndBranch d ->
      let v_pos = Hashtbl.find aenv.var_pos d.var in
      let lower, fp_max_1 = allocate_expr aenv fp_cur d.lower in
      let equal, fp_max_2 = allocate_expr aenv fp_cur d.equal in
      let greater, fp_max_3 = allocate_expr aenv fp_cur d.greater in
      let fp_max = max fp_max_1 (max fp_max_2 fp_max_3) in
      ( mk_aexpr typ
          (AIntCompareAndBranch {lower; equal; greater; cst= d.cst; var= v_pos})
      , fp_max )
  | SStringCompareAndBranch d ->
      let v_pos = Hashtbl.find aenv.var_pos d.var in
      let lower, fp_max_1 = allocate_expr aenv fp_cur d.lower in
      let equal, fp_max_2 = allocate_expr aenv fp_cur d.equal in
      let greater, fp_max_3 = allocate_expr aenv fp_cur d.greater in
      let fp_max = max fp_max_1 (max fp_max_2 fp_max_3) in
      ( mk_aexpr typ
          (AStringCompareAndBranch
             {lower; equal; greater; cst= d.cst; var= v_pos} )
      , fp_max )
  | SContructorCase (v, symb, branches, other) ->
      let v_pos = Hashtbl.find aenv.var_pos v in
      let branches, fp_max =
        Constructor.Map.fold
          (fun cstr arg (branches, fp_max) ->
            let ae, fp_max_arg = allocate_expr aenv fp_cur arg in
            (Constructor.Map.add cstr ae branches, max fp_max fp_max_arg) )
          branches (Constructor.Map.empty, 0)
      in
      let other, fp_max =
        match other with
        | Some o ->
            let other, fp_max_other = allocate_expr aenv fp_cur o in
            (Some other, max fp_max fp_max_other)
        | None ->
            (None, fp_max)
      in
      (mk_aexpr typ (AContructorCase (v_pos, symb, branches, other)), fp_max)
  | SGetField (v, index) ->
      let v_pos = Hashtbl.find aenv.var_pos v in
      (mk_aexpr typ (AGetField (v_pos, index)), fp_cur)

let allocate_fun word_size sfun schema_data =
  let aenv =
    { var_pos= Hashtbl.create 17
    ; word_size
    ; fid= sfun.sfun_id
    ; new_local_blocks= Hashtbl.create 17
    ; inst_pos= Hashtbl.create 17 }
  in
  let index =
    (* the ith argument of the function is at the offset [(index + 2) * word_size]
       of rbp.
       Exemple (x86_64):
         the first one is at 16(%rbp), the second 24(%rbp), etc.
       8(%rbp) is the return address and 0(%rbp) is the old rbp pointer.
       That's why we start index at 2.
    *)
    List.fold_left
      (fun index v ->
        Hashtbl.add aenv.var_pos v (AStackVar (index * word_size)) ;
        index + 1 )
      2 sfun.sfun_vars
  in
  let _ =
    match schema_data with
    | None ->
        (* This is a "regular" function, its required instances are passed as argument. *)
        (* We do the same for the instances required by f. *)
        List.fold_left
          (fun index i ->
            Hashtbl.add aenv.inst_pos i (AStackInst (index * word_size)) ;
            index + 1 )
          index sfun.sfun_insts
    | Some (_, l) ->
        (* This is a function defined inside of an instance. If this instance
           has any instance requirements, they are NOT passed as argument, but
           added at the end of the instance we are defined in (an instance is
           just a block of memory) *)
        List.iter
          (fun (i, i_inst_pos) ->
            Hashtbl.add aenv.inst_pos i
              (AInstInst (index * word_size, i_inst_pos)) )
          l ;
        0
  in
  let afun_body, afun_stack_reserved = allocate_expr aenv 0 sfun.sfun_body in
  let annex_parts = Hashtbl.to_seq aenv.new_local_blocks in
  let fun_label = function_lbl sfun.sfun_id (Option.map fst schema_data) in
  ( { afun_id= sfun.sfun_id
    ; afun_arity= sfun.sfun_arity
    ; afun_body
    ; afun_annex= annex_parts
    ; afun_stack_reserved }
  , fun_label )

let allocate_schema word_size (sshema : sschema) =
  let schema_label = schema_lbl sshema.sschema_id in
  let req_inst_pos =
    List.mapi
      (fun index inst -> (inst, (index + sshema.sschema_nb_funs) * word_size))
      sshema.sschema_insts
  in
  let aschema_funs, aschema_label =
    Function.Map.(
      fold
        (fun fid sfun (afuns, afun_labels) ->
          let afun, fun_label =
            allocate_fun word_size sfun (Some (schema_label, req_inst_pos))
          in
          (add fid afun afuns, add fid fun_label afun_labels) )
        sshema.sschema_funs (empty, empty) )
  in
  ({aschema_id= sshema.sschema_id; aschema_funs; aschema_label}, schema_label)

let allocate_tprogram word_size (p : sprogram) =
  let aschemas, aschema_labels =
    Schema.Map.(
      fold
        (fun sid sshema (aschemas, ashema_labels) ->
          let aschema, ashema_label = allocate_schema word_size sshema in
          (add sid aschema aschemas, add sid ashema_label ashema_labels) )
        p.sschemas (empty, empty) )
  in
  let afuns, afuns_labels =
    Function.Map.(
      fold
        (fun fid sfun (afuns, afun_labels) ->
          let afun, fun_label = allocate_fun word_size sfun None in
          (add fid afun afuns, add fid fun_label afun_labels) )
        p.sfuns (empty, empty) )
  in
  { afuns
  ; aschemas
  ; aschema_labels
  ; aprog_genv= p.sprog_genv
  ; afuns_labels
  ; aprog_main= p.sprog_main }
