open DefaultTypingEnv
open CompileToX86Utils
open CompileInt
open CompileBoolean
open CompileString
open ExprrToX86

let compile_constructor lenv (t, d) cid vargs =
  (*
      alloc (1 + len(vargs)) -> rax
      copy constr_id to 0(%rax)
      move each vargs in to index(%rax)
  *)
  let nb_words = 1 + List.length vargs in
  let t, lenv = alloc lenv t nb_words in
  let t = t ++ movq (imm (Constructor.index_in_symbol cid)) (ind ~ofs:0 rax) in
  let t, d, lenv, index =
    List.fold_left
      (fun (t, d, lenv, index) -> function
        | FromConstant c ->
            let t, d, lenv =
              load_constant lenv (t, d) c
                (ind ~ofs:(index * lenv.word_size) rax)
            in
            (t, d, lenv, index + 1)
        | FromMemory v ->
            let t, d, lenv = load_var lenv (t, d) v !%rbx in
            let t = t ++ movq !%rbp (ind ~ofs:(index * lenv.word_size) rax) in
            (t, d, lenv, index + 1) )
      (t, d, lenv, 1) vargs
  in
  assert (index = nb_words) ;
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
      movq  0(%rax), %rbx
      movq  %rax, %rsi

      (align stack)
      call *%rax
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
  | AFunctionCall (fid, intls, vargs) ->
      compile_fun_call lenv asm fid intls vargs
  | AInstanceCall (inst, fid, vargs) ->
      compile_inst_call lenv asm inst fid vargs
  | AConstructor (cid, vargs) ->
      compile_constructor lenv asm cid vargs
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
