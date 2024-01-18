open X86_64
open CompileUtils

(** [int_neg f lenv x] : load the value of [-x] in [%rax].
    The value of [x] is compiled with [f]. *)
let int_neg f lenv x = f lenv x ++ negq !%rax

(** [int_eq f lenv lhs rhs] : load the value of [lhs == rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_eq f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     sete   %al
     movzbq %al, rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ sete !%al in
  let t = t ++ movzbq !%al rax in
  t

(** [int_neq f lenv lhs rhs] : load the value of [lhs /= rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_neq f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setne  %al
     movzbq %al, rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setne !%al in
  let t = t ++ movzbq !%al rax in
  t

(** [int_add f lenv lhs rhs] : load the value of [lhs + rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_add f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     addq   %rbx, %rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ addq !%rbx !%rax in
  t

(** [int_sub f lenv lhs rhs] : load the value of [lhs - rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_sub f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     movq   %rax, %rbx
     popq   rax
     subq   %rbx, %rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ movq !%rax !%rbx in
  let t = t ++ popq rax in
  let t = t ++ subq !%rbx !%rax in
  t

(** [int_mul f lenv lhs rhs] : load the value of [lhs * rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_mul f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     imulq  %rbx, %rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ imulq !%rbx !%rax in
  t

(** [int_div f lenv lhs rhs] : load the value of [lhs / rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_div f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   %rbx
     pushq  %rax
     pushq  %rbx
     call   boxed_div *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ pushq !%rax in
  let t = t ++ pushq !%rbx in
  let t = t ++ call div_lbl in
  let t = t ++ popnq lenv 2 in
  t

(** [int_gt f lenv lhs rhs] : load the value of [lhs > rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_gt f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setg   %al
     movzbq %al, %rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setg !%al in
  let t = t ++ movzbq !%al rax in
  t

(** [int_ge f lenv lhs rhs] : load the value of [lhs >= rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_ge f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setge  %al
     movzbq %al, %rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setge !%al in
  let t = t ++ movzbq !%al rax in
  t

(** [int_lt f lenv lhs rhs] : load the value of [lhs < rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_lt f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setl   %al
     movzbq %al, %rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setl !%al in
  let t = t ++ movzbq !%al rax in
  t

(** [int_le f lenv lhs rhs] : load the value of [lhs <= rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let int_le f lenv lhs rhs =
  (* lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   rbx
     cmpq   %rax, %rbx
     setle  %al
     movzbq %al, %rax *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ cmpq !%rax !%rbx in
  let t = t ++ setle !%al in
  let t = t ++ movzbq !%al rax in
  t
