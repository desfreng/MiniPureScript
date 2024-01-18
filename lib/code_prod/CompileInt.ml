open X86_64
open CompileUtils

(** [int_neg f asm x] : load the value of [-x] in [%rax].
    The value of [x] is compiled with [f]. *)
let int_neg f lenv (t, d) x =
  let t, d, lenv = f lenv (t, d) x in
  (t ++ negq !%rax, d, lenv)

(** [int_eq f asm lhs rhs] : load the value of [lhs == rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_eq f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     sete   %al
     movzbq %al, rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ sete !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

(** [int_neq f asm lhs rhs] : load the value of [lhs /= rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_neq f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setne  %al
     movzbq %al, rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setne !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

(** [int_add f asm lhs rhs] : load the value of [lhs + rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_add f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     addq   %rbx, %rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ addq !%rbx !%rax in
  (t, d, lenv)

(** [int_sub f asm lhs rhs] : load the value of [lhs - rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_sub f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     movq   %rax, %rbx
     popq   rax
     subq   %rbx, %rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ movq !%rax !%rbx in
  let t = t ++ popq rax in
  let t = t ++ subq !%rbx !%rax in
  (t, d, lenv)

(** [int_mul f asm lhs rhs] : load the value of [lhs * rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_mul f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     imulq  %rbx, %rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ imulq !%rbx !%rax in
  (t, d, lenv)

(** [int_div f asm lhs rhs] : load the value of [lhs / rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_div f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   %rbx
     pushq  %rax
     pushq  %rbx
     call   boxed_div *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ pushq !%rax in
  let t = t ++ pushq !%rbx in
  let t = t ++ call div_lbl in
  let t = t ++ popnq lenv 2 in
  (t, d, lenv)

(** [int_gt f lenv  (t, d) lhs rhs] : load the value of [lhs > rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_gt f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setg   %al
     movzbq %al, %rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setg !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

(** [int_ge f lenv  (t, d) lhs rhs] : load the value of [lhs >= rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_ge f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setge  %al
     movzbq %al, %rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setge !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

(** [int_lt f lenv  (t, d) lhs rhs] : load the value of [lhs < rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_lt f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setl   %al
     movzbq %al, %rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setl !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

(** [int_le f lenv  (t, d) lhs rhs] : load the value of [lhs <= rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_le f lenv (t, d) lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setle  %al
     movzbq %al, %rax *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setle !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)
