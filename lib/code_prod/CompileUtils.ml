open DefaultTypingEnv
open CompileLibC
open AllocAst
open X86_64

module DataHandler : sig
  val add_string : string -> Label.label

  val add_address : label option -> label list -> Label.label

  val declared_data : unit -> [`data] asm
end = struct
  let data = ref nop

  let str_to_lbl = Hashtbl.create 17

  let add_string s =
    match Hashtbl.find_opt str_to_lbl s with
    | Some lbl ->
        lbl
    | None ->
        let str_lbl = Label.string_lbl () in
        let () = Hashtbl.add str_to_lbl s str_lbl in
        str_lbl

  let add_address lbl addrs =
    let addrs_lbl = match lbl with Some lbl -> lbl | None -> jmp_lbl () in
    data := !data ++ label addrs_lbl ++ address addrs ;
    addrs_lbl

  let declared_data () =
    Hashtbl.fold
      (fun str lbl asm -> asm ++ label lbl ++ string str)
      str_to_lbl !data
end

(** [load_constant c dest] : load the value of the constant [c] in [dest]. *)
let load_constant constant dest =
  match constant with
  | Constant.Unit ->
      nop
  | Bool true ->
      movq (imm 1) dest
  | Bool false ->
      movq (imm 0) dest
  | Int i ->
      movq (imm i) dest
  | String txt ->
      let str_label = DataHandler.add_string txt in
      movq (ilab str_label) dest

(** [load_var var_pos dest] : load the value at [var_pos] in [dest]. *)
let load_var var_loc dest =
  match var_loc with
  | AStackVar i ->
      movq (ind ~ofs:i rbp) !%dest
  | AClosVar i ->
      movq (ind ~ofs:i r12) !%dest

(** [load_inst lenv asm inst_loc dest] : load the instance at [inst_loc] in [dest].
    register modified: [dest] only *)
let load_inst inst_loc dest =
  match inst_loc with
  | AStackInst i ->
      movq (ind ~ofs:i rbp) !%dest
  | AClosInst i ->
      movq (ind ~ofs:i r12) !%dest
  | AInstInst (i, j) ->
      (* AInstInst (i, j) ~= j(i(%rbp)) So we do :
         movq i(%rbp) dest
         movq j(dest) dest *)
      movq (ind ~ofs:i rbp) !%dest ++ movq (ind ~ofs:j dest) !%dest

let compile_get_field lenv v_pos index =
  (*
      value(v_pos) -> %rax
      movq [(1 + index) * word_size](%rax) %rax
  *)
  let t = nop in
  let t = t ++ load_var v_pos rax in
  let t = t ++ movq (ind ~ofs:((1 + index) * lenv.word_size) rax) !%rax in
  t

let popnq lenv nb_word =
  let stack_offset = nb_word * lenv.word_size in
  addq (imm stack_offset) !%rsp

let add_pure lenv =
  (* Pure x return the closure of the identity function:

     pure_clos:
       movq 8(%r12), %rax
       ret

     pure:
       pushq $(2 * lenv.word_size)
       call boxed_malloc
       popnq 1
       movq $pure_clos, 0(%rax)
       movq 8(%rsp), %rbx
       movq %rbx, 8(%rax)
       ret
  *)
  let pure_lbl, pure_clos = (function_lbl pure_fid None, local_lbl pure_fid) in
  (* pure closure :*)
  let t = nop in
  let t = t ++ label pure_clos in
  let t = t ++ movq (ind ~ofs:lenv.word_size r12) !%rax in
  let t = t ++ ret in
  (* pure actual code *)
  let t = t ++ label pure_lbl in
  let t = t ++ pushq (imm (2 * lenv.word_size)) in
  let t = t ++ call malloc_lbl in
  let t = t ++ popnq lenv 1 in
  let t = t ++ movq (ilab pure_clos) (ind rax) in
  let t = t ++ movq (ind ~ofs:lenv.word_size rsp) !%rbx in
  let t = t ++ movq !%rbx (ind ~ofs:lenv.word_size rax) in
  let t = t ++ ret in
  (* and we add the label to the environment *)
  let lenv =
    {lenv with funs_lbl= Function.Map.add pure_fid pure_lbl lenv.funs_lbl}
  in
  (t, lenv)

let add_log lenv =
  (*
     log_clos:
       pushq 8(%r12)
       call boxed_puts
       popnq 1
       ret

     log:
       pushq $(2 * lenv.word_size)
       call boxed_malloc
       popnq 1
       movq $pure_clos, 0(%rax)
       movq 8(%rsp), %rbx
       movq %rbx, 8(%rax)
       ret
  *)
  let log_lbl, log_clos = (function_lbl log_fid None, local_lbl log_fid) in
  let t = nop in
  (* pure closure *)
  let t = t ++ label log_clos in
  let t = t ++ pushq (ind ~ofs:lenv.word_size r12) in
  let t = t ++ call puts_lbl in
  let t = t ++ popnq lenv 1 in
  let t = t ++ ret in
  (* pure actual code *)
  let t = t ++ label log_lbl in
  let t = t ++ pushq (imm (2 * lenv.word_size)) in
  let t = t ++ call malloc_lbl in
  let t = t ++ popnq lenv 1 in
  let t = t ++ movq (ilab log_clos) (ind rax) in
  let t = t ++ movq (ind ~ofs:lenv.word_size rsp) !%rbx in
  let t = t ++ movq !%rbx (ind ~ofs:lenv.word_size rax) in
  let t = t ++ ret in
  (* and we add the label to the environment *)
  let lenv =
    {lenv with funs_lbl= Function.Map.add log_fid log_lbl lenv.funs_lbl}
  in
  (t, lenv)

let add_show_int lenv =
  (* A 64bit integer signed cannot take more than 20 characters when converted in decimal.

         .text
     show_int_f: <- This is the function in the instance
         pushq  $20
         call   boxed_malloc
         popnq  1
         ; Need to call boxed_sprintf with args (%rax, $format, 8(%rsp))
         pushq  8(%rsp)
         pushq  $format
         pushq  %rax
         call   boxed_sprintf
         popq   %rax
         popnq  2
         ret

         .data
     show_int: <- This is the instance
         .quad $show_int_f
     format:
         .string "%ld"
  *)
  let fmt_lbl = DataHandler.add_string "%ld" in
  let show_int = schema_lbl show_int_sid in
  let show_int_f = function_lbl show_fid (Some show_int) in
  let show_int = DataHandler.add_address (Some show_int) [show_int_f] in
  let t = nop in
  let t = t ++ label show_int_f in
  let t = t ++ pushq (imm 20) in
  let t = t ++ call malloc_lbl in
  let t = t ++ popnq lenv 1 in
  let t = t ++ pushq (ind ~ofs:lenv.word_size rsp) in
  let t = t ++ pushq (ilab fmt_lbl) in
  let t = t ++ pushq !%rax in
  let t = t ++ call sprintf_lbl in
  let t = t ++ popq rax in
  let t = t ++ popnq lenv 2 in
  let t = t ++ ret in
  let lenv =
    {lenv with schema_lbl= Schema.Map.add show_int_sid show_int lenv.schema_lbl}
  in
  (t, lenv)

let add_show_bool lenv =
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
  let true_str = DataHandler.add_string "true" in
  let false_str = DataHandler.add_string "false" in
  let show_bool = schema_lbl show_bool_sid in
  let sbool_fun, show_false_lbl =
    (function_lbl show_fid (Some show_bool), code_lbl ())
  in
  let show_bool = DataHandler.add_address (Some show_bool) [sbool_fun] in
  let t = nop in
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
  (t, lenv)

let div_lbl = Label.with_prefix "boxed_div"

(** Because the code for the division is quite long, we box it into a assembly
    function *)
let add_div lenv =
  (* - lhs is at 8(%rsp) (we don't make an activation frame, not needed here)
     - rhs is at 16(%rsp)

     The remainder is positive in PureScript, so we tweak the result of the
     division to keep the euclidean division properties. *)
  let div_end, rhs_neg = (Label.code_lbl (), Label.code_lbl ()) in
  let t = nop in
  let t = t ++ label div_lbl in
  let t = t ++ movq (ind ~ofs:(2 * lenv.word_size) rsp) !%rax in
  (* if rhs = 0, return 0 because x/0 = 0 in PureScript... *)
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je div_end in
  (* lhs -> rbx & rhs -> rcx *)
  let t = t ++ movq (ind ~ofs:(1 * lenv.word_size) rsp) !%rbx in
  let t = t ++ movq !%rax !%rcx in
  (* lhs -> rdx::rax and division by rcx *)
  let t = t ++ movq !%rbx !%rax in
  let t = t ++ cqto in
  let t = t ++ idivq !%rcx in
  (* if the remainder is >= 0, we keep the result as it is. *)
  let t = t ++ cmpq (imm 0) !%rdx in
  let t = t ++ jge div_end in
  (* We need to tweak the result here. *)
  let t = t ++ testq !%rcx !%rcx in
  let t = t ++ js rhs_neg in
  (* rhs > 0 so rax -= 1 *)
  let t = t ++ decq !%rax in
  let t = t ++ ret in
  (* rhs < 0  so rax += 1 *)
  let t = t ++ label rhs_neg in
  let t = t ++ incq !%rax in
  (* returns the result *)
  let t = t ++ label div_end in
  let t = t ++ ret in
  (t, lenv)

let add_mod lenv =
  (* - lhs is at 8(%rsp) (we don't make an activation frame, not needed here)
     - rhs is at 16(%rsp)

     The remainder is positive in PureScript, so we tweak the result of the
     division to keep the euclidean division properties. *)
  let mod_fun = function_lbl mod_fid None in
  let mod_end, rhs_neg = (code_lbl (), code_lbl ()) in
  let t = nop in
  let t = t ++ label mod_fun in
  let t = t ++ movq (ind ~ofs:(2 * lenv.word_size) rsp) !%rax in
  (* if rhs = 0, return 0 because x % 0 = 0 in PureScript... *)
  let t = t ++ testq !%rax !%rax in
  let t = t ++ je mod_end in
  (* lhs -> rbx & rhs -> rcx *)
  let t = t ++ movq (ind ~ofs:(1 * lenv.word_size) rsp) !%rbx in
  let t = t ++ movq !%rax !%rcx in
  (* lhs -> rdx::rax and division by rcx *)
  let t = t ++ movq !%rbx !%rax in
  let t = t ++ cqto in
  let t = t ++ idivq !%rcx in
  (* move the remainder in rax *)
  let t = t ++ movq !%rdx !%rax in
  (* if the remainder is >= 0, we keep the result as it is. *)
  let t = t ++ cmpq (imm 0) !%rax in
  let t = t ++ jge mod_end in
  (* We need to tweak the result here. *)
  let t = t ++ testq !%rcx !%rcx in
  let t = t ++ js rhs_neg in
  (* rhs > 0 so we return %rax + rhs (ie. lhs % rhs + rhs) *)
  let t = t ++ addq !%rcx !%rax in
  let t = t ++ ret in
  (* rhs < 0 so we return %rax - rhs (ie. lhs % rhs + |rhs|) *)
  let t = t ++ label rhs_neg in
  let t = t ++ subq !%rcx !%rax in
  (* returns the result *)
  let t = t ++ label mod_end in
  let t = t ++ ret in
  let lenv =
    {lenv with funs_lbl= Function.Map.add mod_fid mod_fun lenv.funs_lbl}
  in
  (t, lenv)

let add_builtins lenv =
  let t = nop in
  let t, lenv =
    let divt, lenv = add_div lenv in
    (t ++ divt, lenv)
  in
  let t, lenv =
    let modt, lenv = add_mod lenv in
    (t ++ modt, lenv)
  in
  let t, lenv =
    let puret, lenv = add_pure lenv in
    (t ++ puret, lenv)
  in
  let t, lenv =
    let logt, lenv = add_log lenv in
    (t ++ logt, lenv)
  in
  let t, lenv =
    let show_int_t, lenv = add_show_int lenv in
    (t ++ show_int_t, lenv)
  in
  let t, lenv =
    let show_bool_t, lenv = add_show_bool lenv in
    (t ++ show_bool_t, lenv)
  in
  (t, lenv)
