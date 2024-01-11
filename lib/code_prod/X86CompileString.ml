open X86CompileUtils

let string_eq f lenv (t, d) lhs rhs =
  (*
     lhs -> rax
     push   %rax
     rhs -> rax
     movq   %rax, %rdi
     popq   %rsi
     (align stack)
     call   strcmp
     (restore stack)
     testq  %rax, %rax
     sete   %al
     movzbq %al, rax
   *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ movq !%rax !%rdi in
  let t, lenv = popq lenv t rsi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "strcmp" in
  let t, lenv = restore_stack lenv t align_data in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ sete !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

let string_neq f lenv (t, d) lhs rhs =
  (*
     lhs -> rax
     push   %rax
     rhs -> rax
     movq   %rax, %rdi
     popq   %rsi
     (align stack)
     call   strcmp
     (restore stack)
     testq  %rax, %rax
     setne   %al
     movzbq %al, rax
   *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ movq !%rax !%rdi in
  let t, lenv = popq lenv t rsi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "strcmp" in
  let t, lenv = restore_stack lenv t align_data in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ setne !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

(** Compute the length of the string [x]. The value is returned in [%rax]. *)
let strlen lenv (t, d) x =
  (*
     movq   x, %rdi
     (align stack)
     call strlen
     (restore stack)
   *)
  let t = t ++ movq x !%rdi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "strlen" in
  let t, lenv = restore_stack lenv t align_data in
  (t, d, lenv)

(** Copy the string [src] into the string [dest]. [dest] is returned in [%rax]. *)
let strcpy lenv (t, d) dest src =
  (*
     movq   dest, %rdi
     movq   src, %rsi
     (align stack)
     call   strcpy
     (restore stack)
   *)
  let t = t ++ movq dest !%rdi in
  let t = t ++ movq src !%rsi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "strcpy" in
  let t, lenv = restore_stack lenv t align_data in
  (t, d, lenv)

(** Append the string [x] at the end of the string [dest]. [dest] is returned in [%rax]. *)
let strcat lenv (t, d) dest x =
  (*
     movq   dest, %rdi
     movq   x, %rsi
     (align stack)
     call   strcat
     (restore stack)
   *)
  let t = t ++ movq dest !%rdi in
  let t = t ++ movq x !%rsi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "strcat" in
  let t, lenv = restore_stack lenv t align_data in
  (t, d, lenv)

(** Concat two string lhs and rhs into %rax. *)
let string_concat f lenv (t, d) lhs rhs =
  (*
     Stack (in x86_64):
              |         |
              |   ...   |
   40(%rsp)   |         |
   32(%rsp)   |   lhs   |  <- Pointer to the LHS string
   24(%rsp)   |   rhs   |  <- Pointer to the RHS string
   16(%rsp)   |  l_lsh  |  <- Lenght of the LHS string
    8(%rsp)   |  l_rsh  |  <- Lenght of the RHS string
    0(%rsp)   |         |  <- rsp

     subq   $32, %rsp
     lhs -> rax
     movq   %rax, 32(%rsp)
     rhs -> rax
     movq   %rax, 24(%rsp)

     ; First call: strlen(lhs)
     strlen (32(%rsp)) -> rax
     movq   %rax, 16(%rsp)

     ; Second call: strlen(rhs)
     strlen (24(%rsp)) -> rax
     movq   %rax, 8(%rsp)

     ; We create the new string (do not forget the '\0' at the end !)
     movq 16(%rsp), %rdi
     addq 8(%rsp), %rdi
     incrq %rdi
     (align stack)
     call "malloc"
     (restore stack)

     strcpy(%rax, 32(%rsp)) -> rax
     strcat(%rax, 16(%rsp)) -> rax

     ; The result is in rax, we restore the stack.
     addq   $32, %rsp

   *)
  let lhs_str = ind ~ofs:(3 * lenv.word_size) rsp in
  let rhs_str = ind ~ofs:(2 * lenv.word_size) rsp in
  let lhs_len = ind ~ofs:(1 * lenv.word_size) rsp in
  let rhs_len = ind ~ofs:(0 * lenv.word_size) rsp in
  let t = t ++ subq (imm (4 * lenv.word_size)) !%rsp in
  (* lhs -> lhs_str *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ movq !%rax lhs_str in
  (* rhs -> rhs_str *)
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ movq !%rax rhs_str in
  (* strlen(lhs_str) -> lhs_len *)
  let t, d, lenv = strlen lenv (t, d) lhs_str in
  let t = t ++ movq !%rax lhs_len in
  (* strlen(rhs_str) -> rhs_len *)
  let t, d, lenv = strlen lenv (t, d) rhs_str in
  let t = t ++ movq !%rax rhs_len in
  (* (lhs_len + rhs_len + 1) -> %rdi *)
  let t = t ++ movq lhs_len !%rdi in
  let t = t ++ addq rhs_len !%rdi in
  let t = t ++ incq !%rdi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "malloc" in
  let t, lenv = restore_stack lenv t align_data in
  let t, d, lenv = strcpy lenv (t, d) !%rax lhs_str in
  let t, d, lenv = strcat lenv (t, d) !%rax rhs_str in
  let t = t ++ addq (imm (4 * lenv.word_size)) !%rsp in
  (t, d, lenv)
