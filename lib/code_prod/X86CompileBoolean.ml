open X86CompileUtils

(** [boolean_and f (t, d) lhs rhs] : load the value of [lhs && rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let boolean_and f lenv (t, d) lhs rhs =
  let and_skip = code_lbl () in
  (*
         lhs -> rax
         testq  %rax, %rax
         je     [and_skip]
         rhs -> rax
     and_skip:
  *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je and_skip in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ label and_skip in
  (t, d, lenv)

(** [boolean_or f (t, d) lhs rhs] : load the value of [lhs || rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let boolean_or f lenv (t, d) lhs rhs =
  (* The order of evaluation DOES import here, if lhs = 1 we do not compile rhs *)
  let or_skip = code_lbl () in
  (*
         lhs -> rax
         testq  %rax, %rax
         jne    [or_skip]
         rhs -> rax
     or_skip:
  *)
  let t, d, lenv = f lenv (t, d) lhs in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ jne or_skip in
  let t, d, lenv = f lenv (t, d) rhs in
  let t = t ++ label or_skip in
  (t, d, lenv)

let boolean_not f lenv (t, d) x =
  (*
      x  -> rax
      not   %rax
      andq  $1, %rax
  *)
  let t, d, lenv = f lenv (t, d) x in
  let t = t ++ notq !%rax in
  let t = t ++ andq (imm 1) !%rax in
  (t, d, lenv)
