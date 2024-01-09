open DefaultTypingEnv
open CompileToX86Utils
open CompileInt
open CompileBoolean
open CompileString

let rec compile_inst lenv (t, d) = function
  | ALocalInst i ->
      load_inst lenv (t, d) i rax
  | AGlobalInst sid ->
      let t = t ++ movq (ilab (Schema.Map.find sid lenv.schema_lbl)) !%rax in
      (t, d, lenv)
  | AGlobalSchema (sid, args, arity) ->
      let t, align_data, lenv = align_stack lenv t arity in
      let t, d, lenv =
        List.fold_left
          (fun (t, d, lenv) i ->
            let t, d, lenv = compile_inst lenv (t, d) i in
            let t, lenv = pushq lenv t !%rax in
            (t, d, lenv) )
          (t, d, lenv) args
      in
      assert (lenv.is_aligned lenv.stack_pos) ;
      let t = t ++ call (Schema.Map.find sid lenv.schema_lbl) in
      let t, lenv = popqn lenv t arity in
      let t, lenv = restore_stack lenv t align_data in
      (t, d, lenv)

let rec compile_equalities lenv asm lhs op rhs =
  let arg_typ = lhs.alloc_expr_typ in
  if is_int_t arg_typ || is_bool_t arg_typ then
    match op with
    | Equal ->
        int_eq compile_aexpr lenv asm lhs rhs
    | NotEqual ->
        int_neq compile_aexpr lenv asm lhs rhs
    | _ ->
        (* Impossible, thanks to compile_aexpr *)
        assert false
  else if is_string_t arg_typ then
    match op with
    | Equal ->
        string_eq compile_aexpr lenv asm lhs rhs
    | NotEqual ->
        string_neq compile_aexpr lenv asm lhs rhs
    | _ ->
        (* Impossible, thanks to compile_aexpr *)
        assert false
  else failwith "Not Implemented"

and compile_int_compare lenv asm lhs op rhs =
  match op with
  | Greater ->
      int_gt compile_aexpr lenv asm lhs rhs
  | GreaterEqual ->
      int_ge compile_aexpr lenv asm lhs rhs
  | Lower ->
      int_lt compile_aexpr lenv asm lhs rhs
  | LowerEqual ->
      int_le compile_aexpr lenv asm lhs rhs
  | _ ->
      (* Impossible, thanks to compile_aexpr *)
      assert false

and compile_arith_op lenv asm lhs op rhs =
  match op with
  | Add ->
      int_add compile_aexpr lenv asm lhs rhs
  | Sub ->
      int_sub compile_aexpr lenv asm lhs rhs
  | Mul ->
      int_mul compile_aexpr lenv asm lhs rhs
  | Div ->
      int_div compile_aexpr lenv asm lhs rhs
  | Mod ->
      int_mod compile_aexpr lenv asm lhs rhs

and compile_boolean_op lenv asm lhs op rhs =
  match op with
  | And ->
      boolean_and compile_aexpr lenv asm lhs rhs
  | Or ->
      boolean_or compile_aexpr lenv asm lhs rhs

and compile_fun_call lenv (t, d) fid intls args =
  (*
      (align stack)
      for each instance (in reverse)
            inst -> rax
            pushq rax
      for each argument (in reverse)
            arg -> rax
            pushq rax
      (assert is stack aligned)
      call fid
      popnq (nb inst + nb args)
      (revert stack)
   *)
  let nb_push = List.length intls + List.length args in
  let t, align_data, lenv = align_stack lenv t nb_push in
  let t, d, lenv =
    List.fold_left
      (fun (t, d, lenv) i ->
        let t, d, lenv = compile_inst lenv (t, d) i in
        let t, lenv = pushq lenv t !%rax in
        (t, d, lenv) )
      (t, d, lenv) (List.rev intls)
  in
  let t, d, lenv =
    List.fold_left
      (fun (t, d, lenv) arg ->
        let t, d, lenv = compile_aexpr lenv (t, d) arg in
        let t, lenv = pushq lenv t !%rax in
        (t, d, lenv) )
      (t, d, lenv) (List.rev args)
  in
  assert (lenv.is_aligned lenv.stack_pos) ;
  let t = t ++ call (Function.Map.find fid lenv.funs_lbl) in
  let t, lenv = popqn lenv t nb_push in
  let t, lenv = restore_stack lenv t align_data in
  (t, d, lenv)

and compile_inst_call lenv (t, d) inst fid args =
  (*
      (align stack)
      rax -> inst
      pushq rax

      for each argument (in reverse)
            arg -> rax
            pushq rax

      movq (nb_args + 1)(%rsp) %rax (retrieve the pushed instance)
      (assert is stack aligned)
      call *(f_index(%rax))
      popnq (1 + nb args)
      (revert stack)
   *)
  let fid_in_call = Option.get @@ Function.index_in_class fid in
  let nb_args = List.length args in
  let nb_push = 1 + nb_args in
  let t, align_data, lenv = align_stack lenv t nb_push in
  let t, d, lenv = compile_inst lenv (t, d) inst in
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv =
    List.fold_left
      (fun (t, d, lenv) arg ->
        let t, d, lenv = compile_aexpr lenv (t, d) arg in
        let t, lenv = pushq lenv t !%rax in
        (t, d, lenv) )
      (t, d, lenv) (List.rev args)
  in
  let t = t ++ movq (ind ~ofs:((nb_push + 1) * lenv.word_size) rsp) !%rax in
  assert (lenv.is_aligned lenv.stack_pos) ;
  let t = t ++ call_star (ind ~ofs:(fid_in_call * lenv.word_size) rax) in
  let t, lenv = popqn lenv t nb_push in
  let t, lenv = restore_stack lenv t align_data in
  (t, d, lenv)

and compile_constructor lenv (t, d) cid args =
  (*
      alloc (1 + len(vargs)) -> rax
      copy constr_id to 0(%rax)
      movq %rax  %rbx
      for each arg:
          push %rbx (save the memory chunk pointer in the stack)
          arg -> rax
          pop %rbx (restore the memory chunk pointer)
          movq %rax index(%rbx)
      movq %rbx %rax
  *)
  let nb_words = 1 + List.length args in
  let t, lenv = alloc lenv t nb_words in
  let t = t ++ movq (imm (Constructor.index_in_symbol cid)) (ind ~ofs:0 rax) in
  let t = t ++ movq !%rax !%rbx in
  let t, d, lenv, index =
    List.fold_left
      (fun (t, d, lenv, index) aexpr ->
        let t, lenv = pushq lenv t !%rbx in
        let t, d, lenv = compile_aexpr lenv (t, d) aexpr in
        let t, lenv = popq lenv t rbx in
        let t = t ++ movq !%rax (ind ~ofs:(index * lenv.word_size) rbx) in
        (t, d, lenv, index + 1) )
      (t, d, lenv, 1) args
  in
  let t = t ++ movq !%rbx !%rax in
  assert (index = nb_words) ;
  (t, d, lenv)

and compile_if lenv (t, d) cond tb fb =
  let else_branch, if_end = (code_lbl (), code_lbl ()) in
  let t, d, lenv = compile_aexpr lenv (t, d) cond in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ jne else_branch in
  let t, d, lenv = compile_aexpr lenv (t, d) tb in
  let t = t ++ jmp if_end in
  let t = t ++ label else_branch in
  let t, d, lenv = compile_aexpr lenv (t, d) fb in
  let t = t ++ label if_end in
  (t, d, lenv)

and compile_do_effect lenv (t, d) x =
  (*
      x -> rax
      movq %rax, %rsi

      (align stack)
      call *(0(%rax))
      (restore stack)
   *)
  let t, d, lenv = compile_aexpr lenv (t, d) x in
  let t = t ++ movq !%rax !%rsi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call_star (ind ~ofs:0 rax) in
  let t, lenv = restore_stack lenv t align_data in
  (t, d, lenv)

and compile_let lenv (t, d) v x y =
  (*
     x -> %rax
     movq   %rax, v(%rbp)
     y -> %rax
  *)
  let t, d, lenv = compile_aexpr lenv (t, d) x in
  let t = t ++ movq !%rax (ind ~ofs:v rbp) in
  compile_aexpr lenv (t, d) y

(** [compile_aexpr asm x] : load the value of [x] in [%rax]. *)
and compile_aexpr lenv asm x =
  match x.alloc_expr with
  | AConstant c ->
      load_constant lenv asm c !%rax
  | AVariable loc ->
      load_var lenv asm loc !%rax
  | ANeg x ->
      int_neg compile_aexpr lenv asm x
  | ANot x ->
      boolean_not compile_aexpr lenv asm x
  | ACompare (lhs, ((Equal | NotEqual) as op), rhs) ->
      compile_equalities lenv asm lhs op rhs
  | ACompare (lhs, ((Lower | LowerEqual | GreaterEqual | Greater) as op), rhs)
    ->
      compile_int_compare lenv asm lhs op rhs
  | AArithOp (lhs, op, rhs) ->
      compile_arith_op lenv asm lhs op rhs
  | ABooleanOp (lhs, op, rhs) ->
      compile_boolean_op lenv asm lhs op rhs
  | AStringConcat (lhs, rhs) ->
      string_concat compile_aexpr lenv asm lhs rhs
  | AFunctionCall (fid, intls, args) ->
      compile_fun_call lenv asm fid intls args
  | AInstanceCall (inst, fid, args) ->
      compile_inst_call lenv asm inst fid args
  | AConstructor (cid, args) ->
      compile_constructor lenv asm cid args
  | AIf (cond, tb, fb) ->
      compile_if lenv asm cond tb fb
  | ALocalClosure _ ->
      assert false
  | ADoEffect x ->
      compile_do_effect lenv asm x
  | ALet (v_pos, x, y) ->
      compile_let lenv asm v_pos x y
  | ACompareAndBranch _ ->
      assert false
  | AContructorCase _ ->
      assert false
  | AGetField (v_pos, index) ->
      compile_get_field lenv asm v_pos index
