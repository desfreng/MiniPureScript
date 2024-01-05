open TypedAst
open AllocAst
open DefaultTypingEnv
open To86Utils

(** [compile_constant asm c] : load the constant [c] in [%rax]. *)
let compile_constant asm = function
  | Constant.TUnit ->
      asm
  | TBool true ->
      add asm (movq (imm 1) !%rax, nop)
  | TBool false ->
      add asm (movq (imm 0) !%rax, nop)
  | TInt i ->
      add asm (movq (imm i) !%rax, nop)
  | TString txt ->
      let str_label = string_lbl () in
      add asm (movq (lab str_label) !%rax, label str_label ++ string txt)

(** [compile_var_loc asm v] : load the value of the variable [v] in [%rax]. *)
let compile_var_loc asm = function
  | ALocalVar i ->
      add asm (movq (ind ~ofs:i rbp) !%rax, nop)
  | AClosVar i ->
      add asm (movq (ind ~ofs:i rsi) !%rax, nop)

(** [compile_neg asm x] : load the value of [-x] in [%rax]. *)
let rec compile_neg asm x =
  let asm = compile_aexpr asm x in
  add_text asm (negq !%rax)

(** [compile_eq asm lhs rhs typ] : load the value of [lhs == rhs] in [%rax]. *)
and compile_eq asm lhs rhs typ =
  if is_bool_t typ || is_int_t typ then
    (* lhs -> rax *)
    let asm = compile_aexpr asm lhs in
    (* rax -> rbx *)
    let asm = add_text asm (movq !%rax !%rbx) in
    (* rhs -> rax *)
    let asm = compile_aexpr asm rhs in
    (* rax - rbx => flags *)
    let asm = add_text asm (cmpq !%rax !%rbx) in
    (* == 0 -> rax  *)
    let asm = add_text asm (sete !%al) in
    let asm = add_text asm (movzbq !%al rax) in
    asm
  else if is_string_t typ then assert false
  else failwith "Not Implemented"

(** [compile_neq asm lhs rhs typ] : load the value of [lhs /= rhs] in [%rax]. *)
and compile_neq asm lhs rhs typ =
  if is_bool_t typ || is_int_t typ then
    (* lhs -> rax *)
    let asm = compile_aexpr asm lhs in
    (* rax -> rbx *)
    let asm = add_text asm (movq !%rax !%rbx) in
    (* rhs -> rax *)
    let asm = compile_aexpr asm rhs in
    (* rax - rbx => flags *)
    let asm = add_text asm (cmpq !%rax !%rbx) in
    (* == 0 -> rax  *)
    let asm = add_text asm (setne !%al) in
    let asm = add_text asm (movzbq !%al rax) in
    asm
  else if is_string_t typ then assert false
  else failwith "Not Implemented"

(** [compile_add asm lhs rhs] : load the value of [lhs + rhs] in [%rax]. *)
and compile_add asm lhs rhs =
  (* The order of evaluation of lhs and rhs does not import here because:
       - They both cannot do any side effect, because their type in Int
         (!= Effect a).
       - They are both required to compute the final value: one of them does
         not terminate iff this computation do not terminate too. *)
  let asm = compile_aexpr asm rhs in
  let asm = add_text asm (movq !%rax !%rbx) in
  let asm = compile_aexpr asm lhs in
  let asm = add_text asm (addq !%rbx !%rax) in
  asm

(** [compile_sub asm lhs rhs] : load the value of [lhs - rhs] in [%rax]. *)
and compile_sub asm lhs rhs =
  (* The order of evaluation of lhs and rhs does not import here because:
       - They both cannot do any side effect, because their type in Int
         (!= Effect a).
       - They are both required to compute the final value: one of them does
         not terminate iff this computation do not terminate too. *)
  let asm = compile_aexpr asm rhs in
  let asm = add_text asm (movq !%rax !%rbx) in
  let asm = compile_aexpr asm lhs in
  let asm = add_text asm (subq !%rbx !%rax) in
  asm

(** [compile_mul asm lhs rhs] : load the value of [lhs * rhs] in [%rax]. *)
and compile_mul asm lhs rhs =
  (* The order of evaluation of lhs and rhs does not import here because:
       - They both cannot do any side effect, because their type in Int
         (!= Effect a).
       - They are both required to compute the final value: one of them does
         not terminate iff this computation do not terminate too. *)
  let asm = compile_aexpr asm rhs in
  let asm = add_text asm (movq !%rax !%rbx) in
  let asm = compile_aexpr asm lhs in
  let asm = add_text asm (imulq !%rbx !%rax) in
  asm

(** [compile_div asm lhs rhs] : load the value of [lhs / rhs] in [%rax]. *)
and compile_div asm lhs rhs =
  let div_lbl = code_lbl () in
  (* lhs -> rax *)
  let asm = compile_aexpr asm lhs in
  (* rax -> rbx *)
  let asm = add_text asm (movq !%rax !%rbx) in
  (* rhs -> rax *)
  let asm = compile_aexpr asm rhs in
  (* if rax = 0 then jmp [div_lbl] *)
  let asm = add_text asm (testq !%rax !%rax) in
  let asm = add_text asm (je div_lbl) in
  (* 0 -> rdx *)
  let asm = add_text asm (movq (imm 0) !%rdx) in
  (* rax, rbx -> rbx, rax *)
  let asm = add_text asm (xchg rax rbx) in
  (* 0::rax / rbx -> rax *)
  let asm = add_text asm (idivq !%rbx) in
  let asm = add_text asm (label div_lbl) in
  asm

(** [compile_mod asm lhs rhs] : load the value of [lhs % rhs] in [%rax]. *)
and compile_mod asm lhs rhs =
  let div_lbl = code_lbl () in
  (* lhs -> rax *)
  let asm = compile_aexpr asm lhs in
  (* rax -> rbx *)
  let asm = add_text asm (movq !%rax !%rbx) in
  (* rhs -> rax *)
  let asm = compile_aexpr asm rhs in
  (* if rax = 0 then jmp [div_lbl] *)
  let asm = add_text asm (testq !%rax !%rax) in
  let asm = add_text asm (je div_lbl) in
  (* 0 -> rdx *)
  let asm = add_text asm (movq (imm 0) !%rdx) in
  (* rax, rbx -> rbx, rax *)
  let asm = add_text asm (xchg rax rbx) in
  (* 0::rax % rbx -> rdx *)
  let asm = add_text asm (idivq !%rbx) in
  (* rdx -> rax*)
  let asm = add_text asm (movq !%rdx !%rax) in
  let asm = add_text asm (label div_lbl) in
  asm

(** [compile_and asm lhs rhs] : load the value of [lhs && rhs] in [%rax]. *)
and compile_and asm lhs rhs =
  (* The order of evaluation DOES import here, if lhs = 0 we do not compile rhs *)
  let end_label = code_lbl () in
  (* lhs -> rax *)
  let asm = compile_aexpr asm lhs in
  (* if rax = 0 then jump [end_label] *)
  let asm = add_text asm (testq !%rax !%rax) in
  let asm = add_text asm (je end_label) in
  (* If we are here, then rhs determine the result.
     rhs -> rax *)
  let asm = compile_aexpr asm rhs in
  (* We add the label here *)
  let asm = add_text asm (label end_label) in
  asm

(** [compile_or asm lhs rhs] : load the value of [lhs || rhs] in [%rax]. *)
and compile_or asm lhs rhs =
  (* The order of evaluation DOES import here, if lhs = 1 we do not compile rhs *)
  let end_label = code_lbl () in
  (* lhs -> rax *)
  let asm = compile_aexpr asm lhs in
  (* if rax = 1 then jump [end_label] *)
  let asm = add_text asm (testq !%rax !%rax) in
  let asm = add_text asm (jne end_label) in
  (* If we are here, then rhs determine the result.
     rhs -> rax *)
  let asm = compile_aexpr asm rhs in
  (* We add the label here *)
  let asm = add_text asm (label end_label) in
  asm

(** [compile_gt asm asm lhs rhs] : load the value of [lhs > rhs] in [%rax]. *)
and compile_gt asm lhs rhs =
  (* lhs -> rax *)
  let asm = compile_aexpr asm lhs in
  (* rax -> rbx *)
  let asm = add_text asm (movq !%rax !%rbx) in
  (* rhs -> rax *)
  let asm = compile_aexpr asm rhs in
  (* rax - rbx => flags *)
  let asm = add_text asm (cmpq !%rax !%rbx) in
  (* > 0 -> rax  *)
  let asm = add_text asm (setg !%al) in
  let asm = add_text asm (movzbq !%al rax) in
  asm

(** [compile_ge asm asm lhs rhs] : load the value of [lhs >= rhs] in [%rax]. *)
and compile_ge asm lhs rhs =
  (* lhs -> rax *)
  let asm = compile_aexpr asm lhs in
  (* rax -> rbx *)
  let asm = add_text asm (movq !%rax !%rbx) in
  (* rhs -> rax *)
  let asm = compile_aexpr asm rhs in
  (* rax - rbx => flags *)
  let asm = add_text asm (cmpq !%rax !%rbx) in
  (* > 0 -> rax  *)
  let asm = add_text asm (setge !%al) in
  let asm = add_text asm (movzbq !%al rax) in
  asm

(** [compile_lt asm asm lhs rhs] : load the value of [lhs < rhs] in [%rax]. *)
and compile_lt asm lhs rhs =
  (* lhs -> rax *)
  let asm = compile_aexpr asm lhs in
  (* rax -> rbx *)
  let asm = add_text asm (movq !%rax !%rbx) in
  (* rhs -> rax *)
  let asm = compile_aexpr asm rhs in
  (* rax - rbx => flags *)
  let asm = add_text asm (cmpq !%rax !%rbx) in
  (* > 0 -> rax  *)
  let asm = add_text asm (setl !%al) in
  let asm = add_text asm (movzbq !%al rax) in
  asm

(** [compile_le asm asm lhs rhs] : load the value of [lhs <= rhs] in [%rax]. *)
and compile_le asm lhs rhs =
  (* lhs -> rax *)
  let asm = compile_aexpr asm lhs in
  (* rax -> rbx *)
  let asm = add_text asm (movq !%rax !%rbx) in
  (* rhs -> rax *)
  let asm = compile_aexpr asm rhs in
  (* rax - rbx => flags *)
  let asm = add_text asm (cmpq !%rax !%rbx) in
  (* > 0 -> rax  *)
  let asm = add_text asm (setle !%al) in
  let asm = add_text asm (movzbq !%al rax) in
  asm

(** [compile_concat asm lhs rhs] : load the value of [lhs <> rhs] in [%rax]. *)
and compile_concat asm lhs rhs =
  ignore (asm, lhs, rhs) ;
  assert false

(** [compile_aexpr asm x] : load the value of [x] in [%rax]. *)
and compile_aexpr asm x =
  match x.aexpr with
  | AConstant c ->
      compile_constant asm c
  | AVariable loc ->
      compile_var_loc asm loc
  | ANeg x ->
      compile_neg asm x
  | ABinOp (lhs, Eq, rhs) ->
      compile_eq asm lhs rhs x.aexpr_typ
  | ABinOp (lhs, Neq, rhs) ->
      compile_neq asm lhs rhs x.aexpr_typ
  | ABinOp (lhs, Gt, rhs) ->
      compile_gt asm lhs rhs
  | ABinOp (lhs, Ge, rhs) ->
      compile_ge asm lhs rhs
  | ABinOp (lhs, Lt, rhs) ->
      compile_lt asm lhs rhs
  | ABinOp (lhs, Le, rhs) ->
      compile_le asm lhs rhs
  | ABinOp (lhs, Plus, rhs) ->
      compile_add asm lhs rhs
  | ABinOp (lhs, Minus, rhs) ->
      compile_sub asm lhs rhs
  | ABinOp (lhs, Mul, rhs) ->
      compile_mul asm lhs rhs
  | ABinOp (lhs, Div, rhs) ->
      compile_div asm lhs rhs
  | ABinOp (lhs, Concat, rhs) ->
      compile_concat asm lhs rhs
  | ABinOp (lhs, And, rhs) ->
      compile_and asm lhs rhs
  | ABinOp (lhs, Or, rhs) ->
      compile_or asm lhs rhs
  | AFunctionCall _ ->
      assert false
  | AFunctionClosure _ ->
      assert false
  | AInstanceCall _ ->
      assert false
  | AInstanceClosure _ ->
      assert false
  | AConstructor _ ->
      assert false
  | AIf _ ->
      assert false
  | ALocalClosure _ ->
      assert false
  | ADoEffect _ ->
      assert false
  | ALet _ ->
      assert false
  | AConstantCase _ ->
      assert false
  | AContructorCase _ ->
      assert false
  | AGetField _ ->
      assert false

let show_int =
  (* let printf_msg = string_lbl () in *)
  (* let data =
      printf_msg *)
  assert false
(*
print_int:
    mov     %rax, %rsi
    mov     $message, %rdi  # arguments pour printf
    mov     $0, %rax
    call    printf
    ret

.data
message:
    .string "%d\n"
 *)

let compile_fun asm afun =
  ignore (asm, afun) ;
  assert false

let compile_aprogram p =
  let asm = (globl (snd p.main), nop) in
  let asm =
    Function.Map.fold (fun _ afun asm -> compile_fun asm afun) p.afuns asm
  in
  asm
