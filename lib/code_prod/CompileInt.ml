open CompileToX86Utils

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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ movq !%rax !%rbx in
  let t, lenv = popq lenv t rax in
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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
  let t = t ++ imulq !%rbx !%rax in
  (t, d, lenv)

(** [int_div f asm lhs rhs] : load the value of [lhs / rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_div f lenv (t, d) lhs rhs =
  let div_end = code_lbl () in
  (*
          lhs -> rax
          pushq  %rax
          rhs -> rax
          popq   rbx
          testq  %rax, %rax
          je     [div_end]
          xorq   %rdx, %rdx
          xchg   %rax, %rbx
          idivq  %rbx
     div_end:
  *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je div_end in
  let t = t ++ xorq !%rdx !%rdx in
  let t = t ++ xchg rax rbx in
  let t = t ++ idivq !%rbx in
  let t = t ++ label div_end in
  (t, d, lenv)

(** [int_mod f asm lhs rhs] : load the value of [lhs % rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_mod f lenv (t, d) lhs rhs =
  (*
          lhs -> rax
          pushq  %rax
          rhs -> rax
          popq   rbx
          testq  %rax, %rax
          je     [mod_end]
          xorq   %rdx, %rdx
          xchg   %rax, %rbx
          idivq  %rbx
          movq   %rdx, %rax
     mod_end:
  *)
  let mod_end = code_lbl () in
  let t, d, lenv = f lenv (t, d) lhs in
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je mod_end in
  let t = t ++ xorq !%rdx !%rdx in
  let t = t ++ xchg rax rbx in
  let t = t ++ idivq !%rbx in
  let t = t ++ movq !%rdx !%rax in
  let t = t ++ label mod_end in
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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
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
  let t, lenv = pushq lenv t !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t, lenv = popq lenv t rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setle !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)
