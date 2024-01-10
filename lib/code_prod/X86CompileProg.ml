open X86CompileUtils
open X86CompileExpr

let compile_fun_part lenv (lbl, fpart) =
  let old_sp_pos = lenv.stack_pos in
  let t, d = (nop, nop) in
  let t, d, lenv = enter_fun lenv (t, d) lbl fpart.local_stack_reserved in
  let t, d, lenv =
    List.fold_left
      (fun (t, d, lenv) e -> compile_aexpr lenv (t, d) e)
      (t, d, lenv) fpart.local_body
  in
  let t, d, lenv = leave_fun lenv (t, d) in
  assert (old_sp_pos = lenv.stack_pos) ;
  (t, d, lenv)

let compile_afun lenv (f_lbl, f) =
  let t, d = (nop, nop) in
  let t, d, lenv =
    Seq.fold_left
      (fun (t, d, lenv) fpart ->
        let pt, pd, lenv = compile_fun_part lenv fpart in
        (t ++ pt, d ++ pd, lenv) )
      (t, d, lenv) f.afun_annex
  in
  let old_sp_pos = lenv.stack_pos in
  let t, d, lenv = enter_fun lenv (t, d) f_lbl f.afun_stack_reserved in
  let t, d, lenv = compile_aexpr lenv (t, d) f.afun_body in
  let t, d, lenv = leave_fun lenv (t, d) in
  assert (old_sp_pos = lenv.stack_pos) ;
  (t, d, lenv)

let compile_schema lenv (s : AllocAst.aschema) =
  let fun_list =
    let fun_list = Function.Map.bindings s.aschema_label in
    let fun_list =
      List.map
        (fun (fid, lbl) -> (Option.get (Function.index_in_class fid), fid, lbl))
        fun_list
    in
    List.sort (fun (id1, _, _) (id2, _, _) -> Int.compare id1 id2) fun_list
  in
  let t, d = (nop, nop) in
  let t, d, lenv =
    List.fold_left
      (fun (t, d, lenv) (_, fid, lbl) ->
        let afun = Function.Map.find fid s.aschema_funs in
        let ft, fd, lenv = compile_afun lenv (lbl, afun) in
        (t ++ ft, d ++ fd, lenv) )
      (t, d, lenv) fun_list
  in
  let nb_arg =
    let sdecl = Schema.Map.find s.aschema_id lenv.schemas in
    List.length sdecl.schema_req
  in
  let schema_lbl = Schema.Map.find s.aschema_id lenv.schema_lbl in
  if nb_arg = 0 then
    (* This is just a jump table in memory *)
    let d =
      d ++ label schema_lbl
      ++ address (List.map (fun (_, _, lbl) -> lbl) fun_list)
    in
    (t, d, lenv)
  else
    let nb_word = List.length fun_list + nb_arg in
    (* This is a function with arguments passed on the stack *)
    let t, d, lenv = enter_fun lenv (t, d) schema_lbl 0 in
    (* We allocate the instance result *)
    let t, lenv = alloc lenv t nb_word in
    (* We copy each function name to its position. *)
    let t, index =
      List.fold_left
        (fun (t, index) (i, _, lbl) ->
          assert (index = i) ;
          ( t ++ movq (ilab lbl) (ind ~ofs:(index * lenv.word_size) rax)
          , index + 1 ) )
        (t, 0) fun_list
    in
    let t, index =
      List.fold_left
        (fun (t, index) rbp_off ->
          ( t
            ++ movq (ind ~ofs:rbp_off rbp) !%rbx
            ++ movq !%rbx (ind ~ofs:(index * lenv.word_size) rax)
          , index + 1 ) )
        (t, index)
        (List.init nb_arg (fun arg_id ->
             lenv.word_size * (arg_id + 2)
             (* The position of the ith argument is (word_size*(i+2)) *) ) )
    in
    assert (index = nb_word) ;
    let t, d, lenv = leave_fun lenv (t, d) in
    (t, d, lenv)

let to_x86 (aprog : AllocAst.aprogram) =
  let constrs =
    Symbol.Map.map (fun sdecl -> sdecl.symbol_constr) aprog.aprog_genv.symbols
  in
  let lenv =
    { schema_lbl= aprog.aschema_labels
    ; funs_lbl= aprog.afuns_labels
    ; constrs
    ; schemas= aprog.aprog_genv.schemas
    ; stack_pos= -8
    ; word_size= 8
    ; is_aligned= (fun i -> i mod 16 == 0) }
  in
  let t, d, lenv = add_builtins lenv in
  let t, d, lenv =
    Schema.Map.fold
      (fun _ aschema (t, d, lenv) ->
        let st, sd, lenv = compile_schema lenv aschema in
        (t ++ st, d ++ sd, lenv) )
      aprog.aschemas (t, d, lenv)
  in
  let t, d, lenv =
    Function.Map.fold
      (fun fid afuns (t, d, lenv) ->
        let fun_lbl = Function.Map.find fid lenv.funs_lbl in
        let ft, fd, lenv = compile_afun lenv (fun_lbl, afuns) in
        (t ++ ft, d ++ fd, lenv) )
      aprog.afuns (t, d, lenv)
  in
  let start_label = "main" in
  (* Is free because function label starts with 'fun_' *)
  let main_label = Function.Map.find aprog.aprog_main lenv.funs_lbl in
  let t = t ++ globl start_label in
  let t, d, lenv = enter_fun lenv (t, d) start_label 0 in
  let t = t ++ call main_label in
  let t = t ++ call_star !%rax in
  let t, d, lenv = leave_fun lenv (t, d) in
  assert (lenv.stack_pos = -8) ;
  {text= t; data= d}
