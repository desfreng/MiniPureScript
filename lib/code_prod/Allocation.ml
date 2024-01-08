open AllocAst

let rec fv e =
  match e.symp_expr with
  | SConstant _ ->
      Variable.Set.empty
  | SVariable v | SGetField (v, _, _) ->
      Variable.Set.singleton v
  | SNeg arg | SNot arg ->
      fv arg
  | SArithOp (lhs, _, rhs)
  | SBooleanOp (lhs, _, rhs)
  | SCompare (lhs, _, rhs)
  | SStringConcat (lhs, rhs) ->
      Variable.Set.union (fv lhs) (fv rhs)
  | SFunctionCall (_, _, l) | SInstanceCall (_, _, l) | SConstructor (_, l) ->
      List.fold_left
        (fun acc -> function
          | Either.Left v ->
              Variable.Set.add v acc
          | Either.Right _ ->
              acc )
        Variable.Set.empty l
  | SBlock l ->
      List.fold_left
        (fun acc e -> Variable.Set.union acc (fv e))
        Variable.Set.empty l
  | SIf (a, b, c) ->
      let s = fv a in
      let s = Variable.Set.union s (fv b) in
      let s = Variable.Set.union s (fv c) in
      s
  | SLet (v, x, y) ->
      let s = Variable.Set.remove v (fv y) in
      let s = Variable.Set.union s (fv x) in
      s
  | SCompareAndBranch {lhs; lower; equal; greater; _} ->
      let s = Variable.Set.singleton lhs in
      let s = Variable.Set.union s (fv lower) in
      let s = Variable.Set.union s (fv equal) in
      let s = Variable.Set.union s (fv greater) in
      s
  | SContructorCase (v, _, branchs, other) ->
      let s = Variable.Set.singleton v in
      let s =
        Constructor.Map.fold
          (fun _ e s -> Variable.Set.union s (fv e))
          branchs s
      in
      let s =
        match other with None -> s | Some o -> Variable.Set.union s (fv o)
      in
      s

let fv =
  List.fold_left (fun acc e -> Variable.Set.union acc (fv e)) Variable.Set.empty

type alloc_env =
  { word_size: int
  ; var_pos: (Variable.t, var_position) Hashtbl.t
  ; new_local_blocks: (label, local_afun_part) Hashtbl.t
  ; fid: Function.t }

let mk_aexpr typ ae = {alloc_expr= ae; alloc_expr_typ= typ}

let get_pos aenv = function
  | Either.Left v ->
      FromMemory (Hashtbl.find aenv.var_pos v)
  | Either.Right cst ->
      FromConstant cst

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
  | SFunctionCall (fid, instl, vargs) ->
      let vargs_pos = List.map (get_pos aenv) vargs in
      (mk_aexpr typ (AFunctionCall (fid, instl, vargs_pos)), fp_cur)
  | SInstanceCall (inst, fid, vargs) ->
      let vargs_pos = List.map (get_pos aenv) vargs in
      (mk_aexpr typ (AInstanceCall (inst, fid, vargs_pos)), fp_cur)
  | SConstructor (cid, vargs) ->
      let vargs_pos = List.map (get_pos aenv) vargs in
      (mk_aexpr typ (AConstructor (cid, vargs_pos)), fp_cur)
  | SIf (cond, tb, fb) ->
      let acond, fp_max_1 = allocate_expr aenv fp_cur cond in
      let atb, fp_max_2 = allocate_expr aenv fp_cur tb in
      let afb, fp_max_3 = allocate_expr aenv fp_cur fb in
      let fp_max = max fp_max_1 (max fp_max_2 fp_max_3) in
      (mk_aexpr typ (AIf (acond, atb, afb)), fp_max)
  | SBlock l -> (
    match l with
    | [] ->
        failwith "Empty do Block."
    | [x] ->
        (* x is of type Effect Unit so we can just return it directly,
           no closure needed (x is already one !) and no label introduced. *)
        allocate_expr aenv fp_cur x
    | l ->
        (* We introduce a new closure with a new label. *)
        let block_lbl = local_lbl aenv.fid in
        (* We compute the free vars in the do block. *)
        let fv_list = Variable.Set.elements (fv l) in
        (* We compute the position of each free variable occuring in this
           closure *)
        let vars_pos = List.map (Hashtbl.find aenv.var_pos) fv_list in
        (* And we build it. *)
        let clos = mk_aexpr typ (ALocalClosure (block_lbl, vars_pos)) in
        (* Now, we process the new label. To do so, we create a new environment
           with the position of each variable in the closure. *)
        let closure_aenv =
          { var_pos= Hashtbl.create 17
          ; word_size= aenv.word_size
          ; fid= aenv.fid
          ; new_local_blocks= aenv.new_local_blocks }
        in
        let _ =
          List.iteri
            (fun index v ->
              (* the ith variable of the closure is a the offset
                 [(index + 1) * word_size]. Exemple :
                 the first one is a 8(%...), the second 16(%...), etc. *)
              Hashtbl.add closure_aenv.var_pos v
                (AClosVar ((index + 1) * aenv.word_size)) )
            fv_list
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
        (clos, fp_cur) )
  | SLet (v, x, y) ->
      let x, fp_max_1 = allocate_expr aenv fp_cur x in
      let fp_cur = fp_cur - aenv.word_size in
      let v_pos = ALocalVar fp_cur in
      Hashtbl.add aenv.var_pos v v_pos ;
      let y, fp_max_2 = allocate_expr aenv fp_cur y in
      (mk_aexpr typ (ALet (v_pos, x, y)), max fp_max_1 fp_max_2)
  | SCompareAndBranch d ->
      let v_pos = Hashtbl.find aenv.var_pos d.lhs in
      let lower, fp_max_1 = allocate_expr aenv fp_cur d.lower in
      let equal, fp_max_2 = allocate_expr aenv fp_cur d.equal in
      let greater, fp_max_3 = allocate_expr aenv fp_cur d.greater in
      let fp_max = max fp_max_1 (max fp_max_2 fp_max_3) in
      ( mk_aexpr typ
          (ACompareAndBranch {lower; equal; greater; rhs= d.rhs; lhs= v_pos})
      , fp_max )
  | SContructorCase (v, v_typ, branches, other) ->
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
      (mk_aexpr typ (AContructorCase (v_pos, v_typ, branches, other)), fp_max)
  | SGetField (v, v_typ, index) ->
      let v_pos = Hashtbl.find aenv.var_pos v in
      (mk_aexpr typ (AGetField (v_pos, v_typ, index)), fp_cur)

let allocate_fun word_size sfun =
  (* This function is compiled as a closure if its return type is Effect a. *)
  let aenv =
    { var_pos= Hashtbl.create 17
    ; word_size
    ; fid= sfun.sfun_id
    ; new_local_blocks= Hashtbl.create 17 }
  in
  let _ =
    (* the ith argument of the function is at the offset [(index + 2) * word_size]
       of rbp.
       Exemple (x86_64):
         the first one is at 16(%rbp), the second 24(%rbp), etc.
       8(%rbp) is the return address and 0(%rbp) is the old rbp pointer.
    *)
    List.iteri
      (fun index v ->
        Hashtbl.add aenv.var_pos v (ALocalVar ((index + 2) * word_size)) )
      sfun.sfun_vars
  in
  let afun_body, afun_stack_reserved = allocate_expr aenv 0 sfun.sfun_body in
  let annex_parts = Hashtbl.to_seq aenv.new_local_blocks in
  let fun_label = function_lbl sfun.sfun_id in
  ( { afun_id= sfun.sfun_id
    ; afun_arity= sfun.sfun_arity
    ; afun_body
    ; afun_annex= annex_parts
    ; afun_stack_reserved }
  , fun_label )

let allocate_schema word_size (sshema : sschema) =
  let aschema_funs, aschema_label =
    Function.Map.(
      fold
        (fun fid sfun (afuns, afun_labels) ->
          let afun, fun_label = allocate_fun word_size sfun in
          (add fid afun afuns, add fid fun_label afun_labels) )
        sshema.sschema_funs (empty, empty) )
  in
  {aschema_id= sshema.sschema_id; aschema_funs; aschema_label}

let allocate_tprogram word_size (p : sprogram) =
  let aschemas = Schema.Map.map (allocate_schema word_size) p.sschemas in
  let afuns, afuns_labels =
    Function.Map.(
      fold
        (fun fid sfun (afuns, afun_labels) ->
          let afun, fun_label = allocate_fun word_size sfun in
          (add fid afun afuns, add fid fun_label afun_labels) )
        p.sfuns (empty, empty) )
  in
  { afuns
  ; aschemas
  ; aprog_genv= p.sprog_genv
  ; afuns_labels
  ; aprog_main= p.sprog_main }
