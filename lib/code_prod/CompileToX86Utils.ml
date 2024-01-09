include X86_64
include AllocAst

type env =
  { schema_lbl: label Schema.map
  ; schema_alloc: aschema Schema.map
  ; funs_lbl: label Function.map
  ; stack_pos: int
  ; word_size: int
  ; is_aligned: int -> bool }

(** [load_constant lenv asm c dest] : load the value of the constant [c] in [dest]. *)
let load_constant lenv (t, d) constant dest =
  match constant with
  | Constant.Unit ->
      (t, d, lenv)
  | Bool true ->
      (t ++ movq (imm 1) dest, d, lenv)
  | Bool false ->
      (t ++ movq (imm 0) dest, d, lenv)
  | Int i ->
      (t ++ movq (imm i) dest, d, lenv)
  | String txt ->
      let str_label = string_lbl () in
      (t ++ movq (lab str_label) dest, label str_label ++ string txt, lenv)

(** [load_var lenv asm var_pos dest] : load the value at [var_pos] in [dest]. *)
let load_var lenv (t, d) var_loc dest =
  match var_loc with
  | AStackVar i ->
      (t ++ movq (ind ~ofs:i rbp) dest, d, lenv)
  | AClosVar i ->
      (t ++ movq (ind ~ofs:i rsi) dest, d, lenv)

(** [load_inst lenv asm inst_loc dest] : load the instance at [inst_loc] in [dest]. *)
let load_inst lenv (t, d) inst_loc dest =
  match inst_loc with
  | AStackInst i ->
      (t ++ movq (ind ~ofs:i rbp) !%dest, d, lenv)
  | AClosInst i ->
      (t ++ movq (ind ~ofs:i rsi) !%dest, d, lenv)
  | AInstInst (i, j) ->
      (* AInstInst (i, j) ~= j(i(%rbp)) So we do :
         movq i(%rbp) dest
         movq j(dest) dest *)
      ( t ++ movq (ind ~ofs:i rbp) !%dest ++ movq (ind ~ofs:j dest) !%dest
      , d
      , lenv )

let compile_get_field lenv (t, d) v_pos index =
  (*
      value(v_pos) -> %rax
      movq [(1 + index) * word_size](%rax) %rax
  *)
  let t, d, lenv = load_var lenv (t, d) v_pos !%rax in
  let t = t ++ movq !%rax (ind ~ofs:((1 + index) * lenv.word_size) rax) in
  (t, d, lenv)

let align_stack lenv t nb_push =
  let stack_offset = ref 0 in
  while
    not
      (lenv.is_aligned
         (lenv.stack_pos - !stack_offset - (nb_push * lenv.word_size)) )
  do
    stack_offset := !stack_offset + lenv.word_size
  done ;
  let t = t ++ subq !%rsp (imm !stack_offset) in
  let lenv = {lenv with stack_pos= lenv.stack_pos - !stack_offset} in
  (t, !stack_offset, lenv)

let restore_stack lenv t stack_offset =
  let t = t ++ addq !%rsp (imm stack_offset) in
  let lenv = {lenv with stack_pos= lenv.stack_pos + stack_offset} in
  (t, lenv)

let pushq lenv t r =
  (t ++ pushq r, {lenv with stack_pos= lenv.stack_pos - lenv.word_size})

let popq lenv t r =
  (t ++ popq r, {lenv with stack_pos= lenv.stack_pos + lenv.word_size})

let popqn lenv t nb_word =
  let stack_offset = nb_word * lenv.word_size in
  ( t ++ addq (imm stack_offset) !%rsp
  , {lenv with stack_pos= lenv.stack_pos + stack_offset} )

(** Perform a call to [malloc], put the result in %rax.
    The following registers are untouched : %rbx, %rbp, %r12, %r13, %r14 & %r15 *)
let alloc lenv t nb_words =
  (*
      movq  $[nb_word * lenv.word_size], %rdi
      xorq  %rax, %rax
      (align stack)
      call  malloc
      (restore stack)
   *)
  let t = t ++ movq (imm (nb_words * lenv.word_size)) !%rdi in
  let t = t ++ xorq !%rax !%rax in
  let t, stack_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "malloc" in
  let t, lenv = restore_stack lenv t stack_data in
  (t, lenv)

(*

let log_fun lenv (text, data) =
  let log_err_lbl = with_prefix (lenv.log_label ^ "_err") in
  let text = text ++ label lenv.log_label in
  (* string to print -> %rdi *)
  let text = text ++ movq (ind ~ofs:8 rsp) !%rdi in
  (* 0 -> %rax *)
  let text = text ++ xorq !%rax !%rax in
  (* align the stack (push 0) *)
  let text = text ++ pushq !%rax in
  (* print the string *)
  let text = text ++ call "puts" in
  (* if rax < 0 then jump to [log_err_lbl] *)
  let text = text ++ cmpq !%rax !%rax in
  let text = text ++ js log_err_lbl in
  (* undo stack aligment (0 -> rax) *)
  let text = text ++ popq rax in
  (* We return *)
  let text = text ++ ret in
  (* Error handling : *)
  let text = text ++ label log_err_lbl in
  (* 1 -> rax *)
  let text = text ++ movq (imm 1) !%rax in
  (* call exit (the stack is aligned !) *)
  let text = text ++ jmp lenv.exit_label in
  (text, data)

 *)
