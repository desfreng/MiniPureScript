include X86_64
include AllocAst
open DefaultTypingEnv

let pp_t ppf t = X86_64.print_program ppf {text= t; data= nop}

type 'a env =
  { schema_lbl: label Schema.map
  ; funs_lbl: label Function.map
  ; constrs: 'a Constructor.map Symbol.map
  ; schemas: schema Schema.map
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
      (t ++ movq (ilab str_label) dest, d ++ label str_label ++ string txt, lenv)

(** [load_var lenv asm var_pos dest] : load the value at [var_pos] in [dest]. *)
let load_var lenv (t, d) var_loc dest =
  match var_loc with
  | AStackVar i ->
      Format.printf "Var is at %i@." i ;
      (t ++ movq (ind ~ofs:i rbp) !%dest, d, lenv)
  | AClosVar i ->
      (t ++ movq (ind ~ofs:i r12) !%dest, d, lenv)

(** [load_inst lenv asm inst_loc dest] : load the instance at [inst_loc] in [dest].
    register modified: [dest] only *)
let load_inst lenv (t, d) inst_loc dest =
  match inst_loc with
  | AStackInst i ->
      (t ++ movq (ind ~ofs:i rbp) !%dest, d, lenv)
  | AClosInst i ->
      (t ++ movq (ind ~ofs:i r12) !%dest, d, lenv)
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
  let t, d, lenv = load_var lenv (t, d) v_pos rax in
  let t = t ++ movq (ind ~ofs:((1 + index) * lenv.word_size) rax) !%rax in
  (t, d, lenv)

let align_stack lenv t nb_push =
  let new_push = ref 0 in
  while
    not
      (lenv.is_aligned
         (lenv.stack_pos - ((!new_push + nb_push) * lenv.word_size)) )
  do
    incr new_push
  done ;
  let stack_offset = !new_push * lenv.word_size in
  if stack_offset = 0 then (t, 0, lenv)
  else
    let t = t ++ subq (imm stack_offset) !%rsp in
    let lenv = {lenv with stack_pos= lenv.stack_pos - stack_offset} in
    (t, stack_offset, lenv)

let restore_stack lenv t stack_offset =
  if stack_offset = 0 then (t, lenv)
  else
    let t = t ++ addq (imm stack_offset) !%rsp in
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
      (align stack)
      call  malloc
      (restore stack)
   *)
  let t = t ++ movq (imm (nb_words * lenv.word_size)) !%rdi in
  let t, stack_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "malloc" in
  let t, lenv = restore_stack lenv t stack_data in
  (t, lenv)

let enter_fun lenv (t, d) lbl res_space =
  let t = t ++ label lbl in
  let t, lenv = pushq lenv t !%rbp in
  let t = t ++ movq !%rsp !%rbp in
  if res_space = 0 then (
    Format.printf "No space for %s@." lbl ;
    (t, d, lenv) )
  else
    let t = t ++ subq (imm res_space) !%rsp in
    (t, d, lenv)

let leave_fun lenv (t, d) =
  let t = t ++ movq !%rbp !%rsp in
  let t, lenv = popq lenv t rbp in
  let t = t ++ ret in
  (t, d, lenv)

let add_pure lenv (t, d) =
  (* Pure x return the closure of the identitu function:

     pure_clos:
       movq 8(%r12), %rax
       ret

     pure:
       alloc 2 -> rax
       movq $pure_clos, 0(%rax)
       movq 8(%rsp), %rbx
       movq %rbx, 8(%rax)
       ret
  *)
  let pure_lbl, pure_clos = (function_lbl pure_fid None, local_lbl pure_fid) in
  (* pure closure :*)
  let t = t ++ label pure_clos in
  let t = t ++ movq (ind ~ofs:lenv.word_size r12) !%rax in
  let t = t ++ ret in
  (* pure actual code *)
  let t = t ++ label pure_lbl in
  let t, lenv = alloc lenv t 2 in
  let t = t ++ movq (ilab pure_clos) (ind rax) in
  let t = t ++ movq (ind ~ofs:lenv.word_size rsp) !%rbx in
  let t = t ++ movq !%rbx (ind ~ofs:lenv.word_size rax) in
  let t = t ++ ret in
  (* and we add the label to the environment *)
  let lenv =
    {lenv with funs_lbl= Function.Map.add pure_fid pure_lbl lenv.funs_lbl}
  in
  (t, d, lenv)

let add_log lenv (t, d) =
  (*
     log_clos:
       movq 8(%r12), %rdi
       (align stack)
       call "puts"
       (restore stack)
       ret

     log:
       alloc 2 -> rax
       movq $pure_clos, 0(%rax)
       movq 8(%rsp), %rbx
       movq %rbx, 8(%rax)
       ret
  *)
  let log_lbl, log_clos = (function_lbl log_fid None, local_lbl log_fid) in
  (* pure closure :*)
  let t = t ++ label log_clos in
  let t = t ++ movq (ind ~ofs:lenv.word_size r12) !%rdi in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "puts" in
  let t, lenv = restore_stack lenv t align_data in
  let t = t ++ ret in
  (* pure actual code *)
  let t = t ++ label log_lbl in
  let t, lenv = alloc lenv t 2 in
  let t = t ++ movq (ilab log_clos) (ind rax) in
  let t = t ++ movq (ind ~ofs:lenv.word_size rsp) !%rbx in
  let t = t ++ movq !%rbx (ind ~ofs:lenv.word_size rax) in
  let t = t ++ ret in
  (* and we add the label to the environment *)
  let lenv =
    {lenv with funs_lbl= Function.Map.add log_fid log_lbl lenv.funs_lbl}
  in
  (t, d, lenv)

let add_show_int lenv (t, d) =
  (* A 64bit integer signed cannot take more than 20 characters when converted in decimal.

         .text
     show_int_f: <- This is the function in the instance
         alloc 20 -> rax
         movq   %rax, %r13 <- calle saved reg
         movq   %r13, %rdi
         movq   $format, %rsi
         movq   8(%rsp), %rdx
         xorq   %rax, %rax
         (align stack)
         call "sprintf"
         (restore stack)
         movq  %r13, %rax
         ret

         .data
     show_int: <- This is the instance
         .quad $show_int_f
     format:
         .string "%d"
  *)
  let format_str = string_lbl () in
  let d = d ++ label format_str ++ string "%d" in
  let show_int = schema_lbl show_int_sid in
  let show_int_f = function_lbl show_fid (Some show_int) in
  let d = d ++ label show_int ++ address [show_int_f] in
  let t = t ++ label show_int_f in
  let t, lenv =
    alloc lenv t ((20 / lenv.word_size) + 1 (* 3 * 8 bytes in x86. *))
  in
  let t = t ++ movq !%rax !%r13 in
  let t = t ++ movq !%r13 !%rdi in
  let t = t ++ movq (ilab format_str) !%rsi in
  let t = t ++ movq (ind ~ofs:lenv.word_size rsp) !%rdx in
  let t = t ++ xorq !%rax !%rax in
  let t, align_data, lenv = align_stack lenv t 0 in
  let t = t ++ call "sprintf" in
  let t, lenv = restore_stack lenv t align_data in
  let t = t ++ movq !%r13 !%rax in
  let t = t ++ ret in
  let lenv =
    {lenv with schema_lbl= Schema.Map.add show_int_sid show_int lenv.schema_lbl}
  in
  (t, d, lenv)

let add_show_bool lenv (t, d) =
  (*
         .text
     show_bool_f: <- This is the function in the instance
         movq 8(%rsp), %rax
         testq  %rax, %rax
         je [show_false]
         mov $true, %rax
         ret

     show_false:
         mov $false, %rax
         ret

         .data
     show_bool: <- This is the instance
         .quad $show_bool_f
     true:
         .string "true"
     false:
         .string "false"
   *)
  let true_str, false_str = (string_lbl (), string_lbl ()) in
  let d =
    d ++ label true_str ++ string "true" ++ label false_str ++ string "false"
  in
  let show_bool = schema_lbl show_bool_sid in
  let sbool_fun, show_false_lbl =
    (function_lbl show_fid (Some show_bool), code_lbl ())
  in
  let d = d ++ label show_bool ++ address [sbool_fun] in
  let t = t ++ label sbool_fun in
  let t = t ++ movq (ind ~ofs:lenv.word_size rsp) !%rax in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je show_false_lbl in
  let t = t ++ movq (ilab true_str) !%rax in
  let t = t ++ ret in
  let t = t ++ label show_false_lbl in
  let t = t ++ movq (ilab false_str) !%rax in
  let t = t ++ ret in
  let lenv =
    { lenv with
      schema_lbl= Schema.Map.add show_bool_sid show_bool lenv.schema_lbl }
  in
  (t, d, lenv)

let add_mod lenv (t, d) =
  let mod_fun = function_lbl mod_fid None in
  let mod_end, rhs_neg = (code_lbl (), code_lbl ()) in
  let t = t ++ label mod_fun in
  let t = t ++ movq (ind ~ofs:lenv.word_size rsp) !%rbx (* lhs -> rbx *) in
  let t =
    t ++ movq (ind ~ofs:(2 * lenv.word_size) rsp) !%rax (* rhs -> rax *)
  in
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je mod_end (* rax = 0 => lhs % rhs = 0 *) in
  let t = t ++ movq !%rax !%rcx (* rhs -> rcx *) in
  let t = t ++ movq !%rbx !%rax in
  let t = t ++ cqto in
  let t = t ++ idivq !%rcx in
  let t = t ++ movq !%rdx !%rax (* lhs "%" rhs -> rax *) in
  let t = t ++ testq !%rbx !%rbx in
  let t = t ++ jns mod_end (* lhs > 0 => result if ok. *) in
  let t = t ++ testq !%rcx !%rcx in
  let t = t ++ js rhs_neg (* rhs < 0 => we return %rax - rhs *) in
  let t = t ++ addq !%rcx !%rax (* rhs > 0 => we return %rax + rhs *) in
  let t = t ++ jmp mod_end in
  let t = t ++ label rhs_neg in
  let t = t ++ subq !%rcx !%rax in
  let t = t ++ label mod_end in
  let t = t ++ ret in
  let lenv =
    {lenv with funs_lbl= Function.Map.add mod_fid mod_fun lenv.funs_lbl}
  in
  (t, d, lenv)

let add_builtins lenv =
  let t, d = (nop, nop) in
  let t, d, lenv = add_mod lenv (t, d) in
  let t, d, lenv = add_pure lenv (t, d) in
  let t, d, lenv = add_log lenv (t, d) in
  let t, d, lenv = add_show_int lenv (t, d) in
  let t, d, lenv = add_show_bool lenv (t, d) in
  (t, d, lenv)
