open X86_64
open CompileLibC
open CompileUtils

let string_eq f lenv (t, d) lhs rhs =
  (*
     lhs -> rax
     push   %rax
     rhs -> rax
     pushq  %rax
     call   boxed_strcmp ; In our case the order of the argument of strcmp does not import
     popnq  2
     testl   %eax, %eax <- strcmp is a Int -> 4 bytes
     sete   %al
     movzbq %al, rax
   *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ pushq !%rax in
  let t = t ++ call strcmp_lbl in
  let t = t ++ popnq lenv 2 in
  let t = t ++ testl !%eax !%eax in
  let t = t ++ sete !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

let string_neq f lenv (t, d) lhs rhs =
  (*
     lhs -> rax
     pushq  %rax
     rhs -> rax
     pushq  %rax
     call   boxed_strcmp ; In our case the order of the argument of strcmp does not import
     popnq  2
     testq  %rax, %rax
     setne   %al
     movzbq %al, rax
   *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ pushq !%rax in
  let t = t ++ call strcmp_lbl in
  let t = t ++ popnq lenv 2 in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ setne !%al in
  let t = t ++ movzbq !%al rax in
  (t, d, lenv)

(** Concat two string lhs and rhs into %rax. *)
let string_concat f lenv (t, d) lhs rhs =
  (*
     lhs -> rax
     pushq  %rax
     rhs -> rax
     popq   %rbx
     pushq  %rax
     pushq  %rbx
     call   strconcat
     popnq  2
   *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ pushq !%rax in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ popq rbx in
  let t = t ++ pushq !%rax in
  let t = t ++ pushq !%rbx in
  let t = t ++ call strconcat_lbl in
  let t = t ++ popnq lenv 2 in
  (t, d, lenv)
