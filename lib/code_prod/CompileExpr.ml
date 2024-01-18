open AllocAst
open X86_64
open DefaultTypingEnv
open CompileUtils
open CompileInt
open CompileBoolean
open CompileString
open CompileLibC

let rec compile_inst lenv = function
  | ALocalInst i ->
      load_inst i rax
  | AGlobalInst sid ->
      movq (ilab (Schema.Map.find sid lenv.schema_lbl)) !%rax
  | AGlobalSchema (sid, args, arity) ->
      let t =
        List.fold_left
          (fun t i -> t ++ compile_inst lenv i ++ pushq !%rax)
          nop (List.rev args)
      in
      let t = t ++ call (Schema.Map.find sid lenv.schema_lbl) in
      let t = t ++ popnq lenv arity in
      t

let rec compile_equalities lenv lhs op rhs =
  let arg_typ = lhs.alloc_expr_typ in
  if is_int_t arg_typ || is_bool_t arg_typ then
    match op with
    | Equal ->
        int_eq compile_aexpr lenv lhs rhs
    | NotEqual ->
        int_neq compile_aexpr lenv lhs rhs
    | _ ->
        (* Impossible, thanks to compile_aexpr *)
        assert false
  else if is_string_t arg_typ then
    match op with
    | Equal ->
        string_eq compile_aexpr lenv lhs rhs
    | NotEqual ->
        string_neq compile_aexpr lenv lhs rhs
    | _ ->
        (* Impossible, thanks to compile_aexpr *)
        assert false
  else (* prevented by the typing *)
    assert false

and compile_int_compare lenv lhs op rhs =
  match op with
  | Greater ->
      int_gt compile_aexpr lenv lhs rhs
  | GreaterEqual ->
      int_ge compile_aexpr lenv lhs rhs
  | Lower ->
      int_lt compile_aexpr lenv lhs rhs
  | LowerEqual ->
      int_le compile_aexpr lenv lhs rhs
  | _ ->
      (* Impossible, thanks to compile_aexpr *)
      assert false

and compile_arith_op lenv lhs op rhs =
  match op with
  | Add ->
      int_add compile_aexpr lenv lhs rhs
  | Sub ->
      int_sub compile_aexpr lenv lhs rhs
  | Mul ->
      int_mul compile_aexpr lenv lhs rhs
  | Div ->
      int_div compile_aexpr lenv lhs rhs
  | Mod ->
      compile_fun_call lenv mod_fid [] [lhs; rhs]

and compile_boolean_op lenv lhs op rhs =
  match op with
  | And ->
      boolean_and compile_aexpr lenv lhs rhs
  | Or ->
      boolean_or compile_aexpr lenv lhs rhs

and compile_fun_call lenv fid intls args =
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
  let t =
    List.fold_left
      (fun t i -> t ++ compile_inst lenv i ++ pushq !%rax)
      nop (List.rev intls)
  in
  let t =
    List.fold_left
      (fun t arg -> t ++ compile_aexpr lenv arg ++ pushq !%rax)
      t (List.rev args)
  in
  let t = t ++ call fun_lbl in
  let t = t ++ popnq lenv nb_push in
  t

and compile_inst_call lenv inst fid args =
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
  let t = nop in
  let t = t ++ compile_inst lenv inst in
  let t = t ++ pushq !%rax in
  let t =
    List.fold_left
      (fun t arg -> t ++ compile_aexpr lenv arg ++ pushq !%rax)
      t (List.rev args)
  in
  let t = t ++ movq (ind ~ofs:(nb_args * lenv.word_size) rsp) !%rax in
  let t = t ++ call_star (ind ~ofs:(fid_in_call * lenv.word_size) rax) in
  let t = t ++ popnq lenv nb_push in
  t

and compile_constructor lenv cid args =
  (*
      pushq   $(1 + len(vargs) * lenv.word_size)
      call    boxed_malloc
      popnq   1
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
  let t = nop in
  let t = t ++ pushq (imm (nb_words * lenv.word_size)) in
  let t = t ++ call malloc_lbl in
  let t = t ++ popnq lenv 1 in
  let t = t ++ movq (imm (Constructor.index_in_symbol cid)) (ind rax) in
  let t = t ++ movq !%rax !%rbx in
  let t, index =
    List.fold_left
      (fun (t, index) aexpr ->
        let t = t ++ pushq !%rbx in
        let t = t ++ compile_aexpr lenv aexpr in
        let t = t ++ popq rbx in
        let t = t ++ movq !%rax (ind ~ofs:(index * lenv.word_size) rbx) in
        (t, index + 1) )
      (t, 1) args
  in
  let t = t ++ movq !%rbx !%rax in
  assert (index = nb_words) ;
  t

and compile_if lenv cond tb fb =
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
  let t = nop in
  let t = t ++ compile_aexpr lenv cond in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je else_branch in
  let t = t ++ compile_aexpr lenv tb in
  let t = t ++ jmp if_end in
  let t = t ++ label else_branch in
  let t = t ++ compile_aexpr lenv fb in
  let t = t ++ label if_end in
  t

and compile_local_closure lenv lbl vars insts closure_size =
  (*
        pushq $(closure_size * lenv.word_size)
        call  malloc
        popnq 1
        movq $lbl 0(%rax)
        for each var:
          load var i(%rax)
        for inst:
          load inst i(%rax)
   *)
  let t = nop in
  let t = t ++ pushq (imm (closure_size * lenv.word_size)) in
  let t = t ++ call malloc_lbl in
  let t = t ++ popnq lenv 1 in
  let t, index = (t ++ movq (ilab lbl) (ind rax), 1) in
  let t, index =
    List.fold_left
      (fun (t, index) var_pos ->
        let t = t ++ load_var var_pos rbx in
        let t = t ++ movq !%rbx (ind ~ofs:(index * lenv.word_size) rax) in
        (t, index + 1) )
      (t, index) vars
  in
  let t, index =
    List.fold_left
      (fun (t, index) inst_pos ->
        let t = t ++ load_inst inst_pos rbx in
        let t = t ++ movq !%rbx (ind ~ofs:(index * lenv.word_size) rax) in
        (t, index + 1) )
      (t, index) insts
  in
  assert (index = closure_size) ;
  t

and compile_do_effect lenv x =
  (*
      pushq %r12
      x ->  rax
      movq  %rax, %r12

      (align stack)
      call *(0(%rax))
      (restore stack)
      popq %r12
   *)
  let t = nop in
  let t = t ++ pushq !%r12 in
  let t = t ++ compile_aexpr lenv x in
  let t = t ++ movq !%rax !%r12 in
  let t = t ++ call_star (ind rax) in
  let t = t ++ popq r12 in
  t

and compile_let lenv v x y =
  (*
     x -> %rax
     movq   %rax, v(%rbp)
     y -> %rax
  *)
  let t = nop in
  let t = t ++ compile_aexpr lenv x in
  let t = t ++ movq !%rax (ind ~ofs:v rbp) in
  let t = t ++ compile_aexpr lenv y in
  t

and compile_int_compare_and_branch lenv var cst lt eq gt =
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
  let t = nop in
  let t = t ++ load_var var rax in
  let t = t ++ cmpq (imm cst) !%rax in
  let t = t ++ jg greater_lbl in
  let t = t ++ js lower_lbl in
  let t = t ++ compile_aexpr lenv eq in
  let t = t ++ jmp end_lbl in
  let t = t ++ label lower_lbl in
  let t = t ++ compile_aexpr lenv lt in
  let t = t ++ jmp end_lbl in
  let t = t ++ label greater_lbl in
  let t = t ++ compile_aexpr lenv gt in
  let t = t ++ label end_lbl in
  t

and compile_string_compare_and_branch lenv var cst lt eq gt =
  (*
      pushq   $cst
      load_var var -> %rax
      pushq   %rax
      call    strcmp
      popnq   2
      testl   %eax, %eax <- strcmp is a Int -> 4 bytes
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
  let string_cst_lbl = DataHandler.add_string cst in
  let lower_lbl, greater_lbl, end_lbl =
    (code_lbl (), code_lbl (), code_lbl ())
  in
  let t = nop in
  let t = t ++ pushq (ilab string_cst_lbl) in
  let t = t ++ load_var var rax in
  let t = t ++ pushq !%rax in
  let t = t ++ call strcmp_lbl in
  let t = t ++ popnq lenv 2 in
  let t = t ++ testl !%eax !%eax in
  let t = t ++ jg greater_lbl in
  let t = t ++ js lower_lbl in
  let t = t ++ compile_aexpr lenv eq in
  let t = t ++ jmp end_lbl in
  let t = t ++ label lower_lbl in
  let t = t ++ compile_aexpr lenv lt in
  let t = t ++ jmp end_lbl in
  let t = t ++ label greater_lbl in
  let t = t ++ compile_aexpr lenv gt in
  let t = t ++ label end_lbl in
  t

and compile_constructor_case lenv v symb branchs other =
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
      Constructor.Set.fold
        (fun cstr l -> (Constructor.index_in_symbol cstr, cstr) :: l)
        cstr_map []
    in
    let cstr_list =
      List.sort (fun (id1, _) (id2, _) -> Int.compare id1 id2) cstr_list
    in
    List.map (fun (id, cstr) -> (id, cstr, code_lbl ())) cstr_list
  in
  let jmp_table_lbl =
    DataHandler.add_address None (List.map (fun (_, _, a) -> a) cstr_list)
  in
  let end_case = code_lbl () in
  let t = nop in
  let t = t ++ load_var v rax in
  let t = t ++ movq (ind rax) !%rax in
  let t = t ++ imulq (imm lenv.word_size) !%rax in
  let t = t ++ addq (ilab jmp_table_lbl) !%rax in
  let t = t ++ jmp_star (ind rax) in
  let t =
    List.fold_left
      (fun t (_, cstr, lbl) ->
        let expr =
          match Constructor.Map.find_opt cstr branchs with
          | Some e ->
              e
          | None ->
              Option.get other
        in
        let t = t ++ label lbl in
        let t = t ++ compile_aexpr lenv expr in
        let t = t ++ jmp end_case in
        t )
      t cstr_list
  in
  let t = t ++ label end_case in
  t

(** [compile_aexpr lenv x] : load the value of [x] in [%rax]. *)
and compile_aexpr lenv x =
  match x.alloc_expr with
  | AConstant c ->
      load_constant c !%rax
  | AVariable loc ->
      load_var loc rax
  | ANeg x ->
      int_neg compile_aexpr lenv x
  | ANot x ->
      boolean_not compile_aexpr lenv x
  | ACompare (lhs, ((Equal | NotEqual) as op), rhs) ->
      compile_equalities lenv lhs op rhs
  | ACompare (lhs, ((Lower | LowerEqual | GreaterEqual | Greater) as op), rhs)
    ->
      compile_int_compare lenv lhs op rhs
  | AArithOp (lhs, op, rhs) ->
      compile_arith_op lenv lhs op rhs
  | ABooleanOp (lhs, op, rhs) ->
      compile_boolean_op lenv lhs op rhs
  | AStringConcat (lhs, rhs) ->
      string_concat compile_aexpr lenv lhs rhs
  | AFunctionCall (fid, intls, args) ->
      compile_fun_call lenv fid intls args
  | AInstanceCall (inst, fid, args) ->
      compile_inst_call lenv inst fid args
  | AConstructor (cid, args) ->
      compile_constructor lenv cid args
  | AIf (cond, tb, fb) ->
      compile_if lenv cond tb fb
  | ALocalClosure (lbl, vars, insts, i) ->
      compile_local_closure lenv lbl vars insts i
  | ADoEffect x ->
      compile_do_effect lenv x
  | ALet (v_pos, x, y) ->
      compile_let lenv v_pos x y
  | AIntCompareAndBranch d ->
      compile_int_compare_and_branch lenv d.var d.cst d.lower d.equal d.greater
  | AStringCompareAndBranch d ->
      compile_string_compare_and_branch lenv d.var d.cst d.lower d.equal
        d.greater
  | AConstructorCase (v, symb, branchs, other) ->
      compile_constructor_case lenv v symb branchs other
  | AGetField (v_pos, index) ->
      compile_get_field lenv v_pos index
