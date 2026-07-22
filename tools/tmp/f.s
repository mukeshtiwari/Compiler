	.text
	.globl _f
_f:
	subq	$32776, %rsp
	leaq	32784(%rsp), %rax
	movq	%rax, 0(%rsp)
	leaq	16(%rsp), %r8
.L1:
	cmpq	$0, %rsi
	jbe	.L90
	leaq	32784(%rsp), %r9
	cmpq	%r9, %r8
	jae	.L90
	movl	28(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, (%r8)
	movl	24(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 4(%r8)
	movl	20(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 8(%r8)
	movl	16(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 12(%r8)
	movl	12(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 16(%r8)
	movl	8(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 20(%r8)
	movl	4(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 24(%r8)
	movl	(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 28(%r8)
	addq	$32, %r8
.L3:
	cmpq	$1, %rsi
	jbe	.L90
	leaq	32784(%rsp), %r9
	cmpq	%r9, %r8
	jae	.L90
	movl	60(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, (%r8)
	movl	56(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 4(%r8)
	movl	52(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 8(%r8)
	movl	48(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 12(%r8)
	movl	44(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 16(%r8)
	movl	40(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 20(%r8)
	movl	36(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 24(%r8)
	movl	32(%rdi), %r9d
	bswap	%r9d
	movl	%r9d, 28(%r8)
	addq	$32, %r8
.L5:
	leaq	80(%rsp), %r9
	cmpq	%r9, %r8
	jb	.L90
	movl	-64(%r8), %r9d
	movl	-32(%r8), %r10d
	addl	%r10d, %r9d
	movl	%r9d, -64(%r8)
	movl	-60(%r8), %r9d
	movl	-28(%r8), %r10d
	adcl	%r10d, %r9d
	movl	%r9d, -60(%r8)
	movl	-56(%r8), %r9d
	movl	-24(%r8), %r10d
	adcl	%r10d, %r9d
	movl	%r9d, -56(%r8)
	movl	-52(%r8), %r9d
	movl	-20(%r8), %r10d
	adcl	%r10d, %r9d
	movl	%r9d, -52(%r8)
	movl	-48(%r8), %r9d
	movl	-16(%r8), %r10d
	adcl	%r10d, %r9d
	movl	%r9d, -48(%r8)
	movl	-44(%r8), %r9d
	movl	-12(%r8), %r10d
	adcl	%r10d, %r9d
	movl	%r9d, -44(%r8)
	movl	-40(%r8), %r9d
	movl	-8(%r8), %r10d
	adcl	%r10d, %r9d
	movl	%r9d, -40(%r8)
	movl	-36(%r8), %r9d
	movl	-4(%r8), %r10d
	adcl	%r10d, %r9d
	movl	%r9d, -36(%r8)
	subq	$32, %r8
.L6:
	cmpq	$0, %rcx
	jbe	.L90
	leaq	48(%rsp), %r9
	cmpq	%r9, %r8
	jb	.L90
	movl	-32(%r8), %r9d
	bswap	%r9d
	movl	%r9d, 28(%rdx)
	movl	-28(%r8), %r9d
	bswap	%r9d
	movl	%r9d, 24(%rdx)
	movl	-24(%r8), %r9d
	bswap	%r9d
	movl	%r9d, 20(%rdx)
	movl	-20(%r8), %r9d
	bswap	%r9d
	movl	%r9d, 16(%rdx)
	movl	-16(%r8), %r9d
	bswap	%r9d
	movl	%r9d, 12(%rdx)
	movl	-12(%r8), %r9d
	bswap	%r9d
	movl	%r9d, 8(%rdx)
	movl	-8(%r8), %r9d
	bswap	%r9d
	movl	%r9d, 4(%rdx)
	movl	-4(%r8), %r9d
	bswap	%r9d
	movl	%r9d, (%rdx)
	subq	$32, %r8
.L8:
	jmp	.L90
.L90:
	addq	$32776, %rsp
	ret
