	.text
fun_mod:
	movq 8(%rsp), %rbx
	movq 16(%rsp), %rax
	testq %rax, %rax
	je L_2
	movq %rax, %rcx
	movq %rbx, %rax
	cqto
	idivq %rcx
	movq %rdx, %rax
	testq %rbx, %rbx
	jns L_2
	testq %rcx, %rcx
	js L_1
	addq %rcx, %rax
	jmp L_2
L_1:
	subq %rcx, %rax
L_2:
	ret
pure_do_block_1:
	movq 8(%r12), %rax
	ret
fun_pure:
	movq $16, %rdi
	subq $8, %rsp
	call malloc
	addq $8, %rsp
	movq $pure_do_block_1, 0(%rax)
	movq 8(%rsp), %rbx
	movq %rbx, 8(%rax)
	ret
log_do_block_1:
	movq 8(%r12), %rdi
	subq $8, %rsp
	call puts
	addq $8, %rsp
	ret
fun_log:
	movq $16, %rdi
	subq $8, %rsp
	call malloc
	addq $8, %rsp
	movq $log_do_block_1, 0(%rax)
	movq 8(%rsp), %rbx
	movq %rbx, 8(%rax)
	ret
fun_schema_2_show:
	movq $24, %rdi
	subq $8, %rsp
	call malloc
	addq $8, %rsp
	movq %rax, %r13
	movq %r13, %rdi
	movq $string_1, %rsi
	movq 8(%rsp), %rdx
	xorq %rax, %rax
	subq $8, %rsp
	call sprintf
	addq $8, %rsp
	movq %r13, %rax
	ret
fun_schema_1_show:
	movq 8(%rsp), %rax
	testq %rax, %rax
	je L_3
	movq $string_3, %rax
	ret
L_3:
	movq $string_2, %rax
	ret
fun_main:
	pushq %rbp
	movq %rsp, %rbp
	subq $8, %rsp
	movq $string_4, %rax
	pushq %rax
	call fun_log
	addq $8, %rsp
	addq $8, %rsp
	movq %rbp, %rsp
	popq %rbp
	ret
	.globl	main
main:
	pushq %rbp
	movq %rsp, %rbp
	call fun_main
	movq %rax, %r12
	call *0(%rax)
	xorq %rax, %rax
	movq %rbp, %rsp
	popq %rbp
	ret
	.data
string_1:
	.string "%d"
schema_2:
	.quad fun_schema_2_show
string_3:
	.string "true"
string_2:
	.string "false"
schema_1:
	.quad fun_schema_1_show
string_4:
	.string "He llo e "
