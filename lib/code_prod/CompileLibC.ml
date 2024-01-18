open AllocAst
open X86_64

let enter_fun t lbl res_space =
  let t = t ++ label lbl in
  let t = t ++ pushq !%rbp in
  let t = t ++ movq !%rsp !%rbp in
  if res_space = 0 then t
  else
    let t = t ++ subq (imm res_space) !%rsp in
    t

let leave_fun t =
  let t = t ++ movq !%rbp !%rsp in
  let t = t ++ popq rbp in
  let t = t ++ ret in
  t

let malloc_lbl = Label.with_prefix "boxed_malloc"

let add_malloc lenv (t, d) =
  (*
   boxed_malloc:
      (enter function)
      andq $(-16) $rsp
      movq 16(%rbp) %rdi
      call malloc
      (leave fun)
   *)
  let t = enter_fun t malloc_lbl 0 in
  let t = t ++ lenv.align_stack () in
  let t = t ++ movq (ind ~ofs:(2 * lenv.word_size) rbp) !%rdi in
  let t = t ++ call "malloc" in
  let t = leave_fun t in
  (t, d, lenv)

let puts_lbl = Label.with_prefix "boxed_puts"

let add_puts lenv (t, d) =
  (*
   boxed_puts:
      (enter function)
      andq $(-16) $rsp
      movq 16(%rbp) %rdi
      call puts
      (leave fun)
   *)
  let t = enter_fun t puts_lbl 0 in
  let t = t ++ lenv.align_stack () in
  let t = t ++ movq (ind ~ofs:(2 * lenv.word_size) rbp) !%rdi in
  let t = t ++ call "puts" in
  let t = leave_fun t in
  (t, d, lenv)

let sprintf_lbl = Label.with_prefix "boxed_sprintf"

let add_sprintf lenv (t, d) =
  (*
   boxed_sprintf:
      (enter function)
      andq $(-16) $rsp
      movq 16(%rbp) %rdi
      movq 24(%rbp) %rsi
      movq 32(%rbp) %rdx
      call sprintf
      (leave fun)
   *)
  let t = enter_fun t sprintf_lbl 0 in
  let t = t ++ lenv.align_stack () in
  let t = t ++ movq (ind ~ofs:(2 * lenv.word_size) rbp) !%rdi in
  let t = t ++ movq (ind ~ofs:(3 * lenv.word_size) rbp) !%rsi in
  let t = t ++ movq (ind ~ofs:(4 * lenv.word_size) rbp) !%rdx in
  let t = t ++ call "sprintf" in
  let t = leave_fun t in
  (t, d, lenv)

let strcmp_lbl = Label.with_prefix "boxed_strcmp"

let add_strcmp lenv (t, d) =
  (*
   boxed_strcmp:
      (enter function)
      andq $(-16) $rsp
      movq 16(%rbp) %rdi
      movq 24(%rbp) %rsi
      call strcmp
      (leave fun)
   *)
  let t = enter_fun t strcmp_lbl 0 in
  let t = t ++ lenv.align_stack () in
  let t = t ++ movq (ind ~ofs:(2 * lenv.word_size) rbp) !%rdi in
  let t = t ++ movq (ind ~ofs:(3 * lenv.word_size) rbp) !%rsi in
  let t = t ++ call "strcmp" in
  let t = leave_fun t in
  (t, d, lenv)

let strconcat_lbl = Label.with_prefix "boxed_strconcat"

let add_strconcat lenv (t, d) =
  (*
    Stack (in x86_64):
              |         |
              |   ...   |
   24(%rbp)   |   rhs   |  <- Pointer to the RHS string
   16(%rbp)   |   lhs   |  <- Pointer to the LHS string
              +---------+
    8(%rbp)   |   ret   |  <- return address
    0(%rbp)   | old_rbp |  <- old %rbp
              +---------+
              |         |  <- rsp

    Registers:
      - LHS Lenght: %r13

    pushq   %rbp
    movq    %rsp, %rbp
    andq    $-16, %rsp

    movq    16(%rbp), %rdi
    call    strlen
    movq    %rax, %r13

    movq    24(%rbp), %rdi
    call    strlen

    leaq    0(%rax, %r13), %rdi
    incq    %rdi
    call    malloc

    movq    %rax, %rdi
    movq    16(%rbp), %rsi
    call    strcpy

    movq    %rax, %rdi
    movq    24(%rbp), %rsi
    call    strcat

    leave
    ret
   *)
  let t = enter_fun t strconcat_lbl (3 * lenv.word_size) in
  let t = t ++ lenv.align_stack () in
  (* Compute the length of lhs into r13 *)
  let t = t ++ movq (ind ~ofs:(2 * lenv.word_size) rbp) !%rdi in
  let t = t ++ call "strlen" in
  let t = t ++ movq !%rax !%r13 in
  (* Compute the length of rhs into rax *)
  let t = t ++ movq (ind ~ofs:(3 * lenv.word_size) rbp) !%rdi in
  let t = t ++ call "strlen" in
  (* Allocate the new string *)
  let t = t ++ leaq (ind rax ~index:r13) rdi in
  let t = t ++ incq !%rdi in
  let t = t ++ call "malloc" in
  (* Copy lhs at the begining of the new string *)
  let t = t ++ movq !%rax !%rdi in
  let t = t ++ movq (ind ~ofs:(2 * lenv.word_size) rbp) !%rsi in
  let t = t ++ call "strcpy" in
  (* Copy rhs after lhs in the new string *)
  let t = t ++ movq !%rax !%rdi in
  let t = t ++ movq (ind ~ofs:(3 * lenv.word_size) rbp) !%rsi in
  let t = t ++ call "strcat" in
  (* The new string is in rax *)
  let t = leave_fun t in
  (t, d, lenv)

let add_boxed_libc lenv (t, d) =
  let t, d, lenv = add_malloc lenv (t, d) in
  let t, d, lenv = add_puts lenv (t, d) in
  let t, d, lenv = add_sprintf lenv (t, d) in
  let t, d, lenv = add_strcmp lenv (t, d) in
  let t, d, lenv = add_strconcat lenv (t, d) in
  (t, d, lenv)
