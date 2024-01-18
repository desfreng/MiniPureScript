open X86_64
open CompileLibC
open CompileUtils

let string_eq f lenv lhs rhs =
  (*
     lhs -> rax
     push   %rax
     rhs -> rax
     pushq  %rax
     call   boxed_strcmp ; In our case the order of the argument of strcmp does not import
     popnq  2
     testl  %eax, %eax <- strcmp returns an int -> 4 bytes
     sete   %al
     movzbq %al, rax
   *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ pushq !%rax in
  let t = t ++ call strcmp_lbl in
  let t = t ++ popnq lenv 2 in
  let t = t ++ testl !%eax !%eax in
  let t = t ++ sete !%al in
  let t = t ++ movzbq !%al rax in
  t

let string_neq f lenv lhs rhs =
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
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ pushq !%rax in
  let t = t ++ call strcmp_lbl in
  let t = t ++ popnq lenv 2 in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ setne !%al in
  let t = t ++ movzbq !%al rax in
  t

(** Concat two string lhs and rhs into %rax. *)
let string_concat f lenv lhs rhs =
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
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ pushq !%rax in
  let t = t ++ f lenv rhs in
  let t = t ++ popq rbx in
  let t = t ++ pushq !%rax in
  let t = t ++ pushq !%rbx in
  let t = t ++ call strconcat_lbl in
  let t = t ++ popnq lenv 2 in
  t
