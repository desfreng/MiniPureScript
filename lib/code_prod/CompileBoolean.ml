open X86_64

(** [boolean_and f lenv lhs rhs] : load the value of [lhs && rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let boolean_and f lenv lhs rhs =
  let and_skip = Label.code_lbl () in
  (*
         lhs -> rax
         testq  %rax, %rax
         je     [and_skip]
         rhs -> rax
     and_skip:
  *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je and_skip in
  let t = t ++ f lenv rhs in
  let t = t ++ label and_skip in
  t

(** [boolean_or f lenv lhs rhs] : load the value of [lhs || rhs] in [%rax].
    The value of [lhs] and [rhs] is compiled with [f]. *)
let boolean_or f lenv lhs rhs =
  (* The order of evaluation DOES import here, if lhs = 1 we do not compile rhs *)
  let or_skip = Label.code_lbl () in
  (*
         lhs -> rax
         testq  %rax, %rax
         jne    [or_skip]
         rhs -> rax
     or_skip:
  *)
  let t = nop in
  let t = t ++ f lenv lhs in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ jne or_skip in
  let t = t ++ f lenv rhs in
  let t = t ++ label or_skip in
  t

let boolean_not f lenv x =
  (*
      x  -> rax
      notq  %rax
      andq  $1, %rax
  *)
  let t = nop in
  let t = t ++ f lenv x in
  let t = t ++ notq !%rax in
  let t = t ++ andq (imm 1) !%rax in
  t
