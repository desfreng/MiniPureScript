open DefaultTypingEnv
open X86CompileUtils
open X86CompileInt
open X86CompileBoolean
open X86CompileString

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
          (t, d, lenv) (List.rev args)
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
      compile_fun_call lenv asm mod_fid [] [lhs; rhs]

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
  let fun_lbl = Function.Map.find fid lenv.funs_lbl in
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
  let t = t ++ call fun_lbl in
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

      movq (nb_args)(%rsp) %rax (retrieve the pushed instance)
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
  let t = t ++ movq (ind ~ofs:(nb_args * lenv.word_size) rsp) !%rax in
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
  let t = t ++ movq (imm (Constructor.index_in_symbol cid)) (ind rax) in
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
  (*
        cond -> rax
        testq   %rax, %rax
        je     else_branch
        tb -> rax
        jmp     if_end
    else_branch:
        fb -> rax
    if_end:
  *)
  let else_branch, if_end = (code_lbl (), code_lbl ()) in
  let t, d, lenv = compile_aexpr lenv (t, d) cond in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je else_branch in
  let t, d, lenv = compile_aexpr lenv (t, d) tb in
  let t = t ++ jmp if_end in
  let t = t ++ label else_branch in
  let t, d, lenv = compile_aexpr lenv (t, d) fb in
  let t = t ++ label if_end in
  (t, d, lenv)

and compile_local_closure lenv (t, d) lbl vars insts closure_size =
  (*
        alloc closure_size -> rax
        movq $lbl 0(%rax)
        for each var:
          load var i(%rax)
        for inst:
          load inst i(%rax)
   *)
  let t, lenv = alloc lenv t closure_size in
  let t, index = (t ++ movq (ilab lbl) (ind rax), 1) in
  let t, d, lenv, index =
    List.fold_left
      (fun (t, d, lenv, index) var_pos ->
        let t, d, lenv = load_var lenv (t, d) var_pos rbx in
        let t = t ++ movq !%rbx (ind ~ofs:(index * lenv.word_size) rax) in
        (t, d, lenv, index + 1) )
      (t, d, lenv, index) vars
  in
  let t, d, lenv, index =
    List.fold_left
      (fun (t, d, lenv, index) inst_pos ->
        let t, d, lenv = load_inst lenv (t, d) inst_pos rbx in
        let t = t ++ movq !%rbx (ind ~ofs:(index * lenv.word_size) rax) in
        (t, d, lenv, index + 1) )
      (t, d, lenv, index) insts
  in
  assert (index = closure_size) ;
  (t, d, lenv)

and compile_do_effect lenv (t, d) x =
  (*
      pushq %r12
      x ->  rax
      movq  %rax, %r12

      (align stack)
      call *(0(%rax))
      (restore stack)
      popq %r12
   *)
  let t, lenv = pushq lenv t !%r12 in
  let t, d, lenv = compile_aexpr lenv (t, d) x in
  let t = t ++ movq !%rax !%r12 in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call_star (ind rax) in
  let t, lenv = restore_stack lenv t align_data in
  let t, lenv = popq lenv t r12 in
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

and compile_int_compare_and_branch lenv (t, d) var cst lt eq gt =
  (*
      load_var var -> rax
      cmpq    %rax $cst
      jg      greater
      js      lower
      equal -> rax
      jmp     branch_end
  lower:
      lower -> rax
      jmp branch_end
  greater:
      greater -> rax
  end:
  *)
  let lower_lbl, greater_lbl, end_lbl =
    (code_lbl (), code_lbl (), code_lbl ())
  in
  let t, d, lenv = load_var lenv (t, d) var rax in
  let t = t ++ cmpq (imm cst) !%rax in
  let t = t ++ jg greater_lbl in
  let t = t ++ js lower_lbl in
  let t, d, lenv = compile_aexpr lenv (t, d) eq in
  let t = t ++ jmp end_lbl in
  let t = t ++ label lower_lbl in
  let t, d, lenv = compile_aexpr lenv (t, d) lt in
  let t = t ++ jmp end_lbl in
  let t = t ++ label greater_lbl in
  let t, d, lenv = compile_aexpr lenv (t, d) gt in
  let t = t ++ label end_lbl in
  (t, d, lenv)

and compile_string_compare_and_branch lenv (t, d) var cst lt eq gt =
  (*
      load_var var -> %rdi
      movq    $cst, %rsi
      (align stack)
      call  strcmp
      (restore stack)
      testq   %eax, %eax <- strcmp is a Int -> 4 bytes
      jg      greater
      js      lower
      equal -> rax
      jmp     branch_end
  lower:
      lower -> rax
      jmp branch_end
  greater:
      greater -> rax
  branch_end:
  *)
  let lower_lbl, greater_lbl, end_lbl, string_cst =
    (code_lbl (), code_lbl (), code_lbl (), string_lbl ())
  in
  let d = d ++ label string_cst ++ string cst in
  let t, d, lenv = load_var lenv (t, d) var rdi in
  let t = t ++ movq (ilab string_cst) !%rsi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "strcmp" in
  let t, lenv = restore_stack lenv t align_data in
  let t = t ++ testl !%eax !%eax in
  let t = t ++ jg greater_lbl in
  let t = t ++ js lower_lbl in
  let t, d, lenv = compile_aexpr lenv (t, d) eq in
  let t = t ++ jmp end_lbl in
  let t = t ++ label lower_lbl in
  let t, d, lenv = compile_aexpr lenv (t, d) lt in
  let t = t ++ jmp end_lbl in
  let t = t ++ label greater_lbl in
  let t, d, lenv = compile_aexpr lenv (t, d) gt in
  let t = t ++ label end_lbl in
  (t, d, lenv)

and compile_constructor_case lenv (t, d) v symb branchs other =
  (*
     We have in memory a jump table. For each branch we have the address of
     code to execute.

          .data

     cstr_jmp_lbl :
          code_cstr1
          code_cstr2
          ...
          code_cstrn

          .text
          load_var v -> rax
          movq  0(%rax), %rax
          mulq  [word_size], %rax
          addq  $cstr_jmp_lbl, %rax
          jmp   %(rax)

     code_cstr1:
          branch(cstr1) -> rax
          (if cstr1 not int branch, it is other !)
          jmp end

     code_cstr2:
          ...

     code_cstrn:
          ...

     end:
  *)
  let cstr_list =
    let cstr_map = Symbol.Map.find symb lenv.constrs in
    let cstr_list =
      Constructor.Map.fold
        (fun cstr _ l -> (Constructor.index_in_symbol cstr, cstr) :: l)
        cstr_map []
    in
    let cstr_list =
      List.sort (fun (id1, _) (id2, _) -> Int.compare id1 id2) cstr_list
    in
    List.map (fun (id, cstr) -> (id, cstr, code_lbl ())) cstr_list
  in
  let jmp_table_lbl, end_case = (jmp_lbl (), code_lbl ()) in
  let d =
    d ++ label jmp_table_lbl
    ++ address (List.map (fun (_, _, a) -> a) cstr_list)
  in
  let t, d, lenv = load_var lenv (t, d) v rax in
  let t = t ++ movq (ind rax) !%rax in
  let t = t ++ imulq (imm lenv.word_size) !%rax in
  let t = t ++ addq (ilab jmp_table_lbl) !%rax in
  let t = t ++ jmp_star (ind rax) in
  let t, d, lenv =
    List.fold_left
      (fun (t, d, lenv) (_, cstr, lbl) ->
        let expr =
          match Constructor.Map.find_opt cstr branchs with
          | Some e ->
              e
          | None ->
              Option.get other
        in
        let t = t ++ label lbl in
        let t, d, lenv = compile_aexpr lenv (t, d) expr in
        let t = t ++ jmp end_case in
        (t, d, lenv) )
      (t, d, lenv) cstr_list
  in
  let t = t ++ label end_case in
  (t, d, lenv)

(** [compile_aexpr asm x] : load the value of [x] in [%rax]. *)
and compile_aexpr lenv asm x =
  let old_pos = lenv.stack_pos in
  let t, d, lenv =
    match x.alloc_expr with
    | AConstant c ->
        load_constant lenv asm c !%rax
    | AVariable loc ->
        load_var lenv asm loc rax
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
    | ALocalClosure (lbl, vars, insts, i) ->
        compile_local_closure lenv asm lbl vars insts i
    | ADoEffect x ->
        compile_do_effect lenv asm x
    | ALet (v_pos, x, y) ->
        compile_let lenv asm v_pos x y
    | AIntCompareAndBranch d ->
        compile_int_compare_and_branch lenv asm d.var d.cst d.lower d.equal
          d.greater
    | AStringCompareAndBranch d ->
        compile_string_compare_and_branch lenv asm d.var d.cst d.lower d.equal
          d.greater
    | AContructorCase (v, symb, branchs, other) ->
        compile_constructor_case lenv asm v symb branchs other
    | AGetField (v_pos, index) ->
        compile_get_field lenv asm v_pos index
  in
  assert (lenv.stack_pos = old_pos) ;
  (t, d, lenv)
