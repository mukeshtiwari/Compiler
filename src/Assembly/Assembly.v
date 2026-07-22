From Bytecode Require Import Bytecode.
From compcert.common Require Import AST.
From compcert.lib Require Import Integers.
From compcert.x86 Require Import Asm.
From Stdlib Require Import Utf8 List ZArith Arith.PeanoNat.
Import ListNotations.


Section Comp.

	Definition bytecode_signature : signature :=
		mksignature [Xptr; Xint; Xptr; Xint] Xvoid cc_default.

	Definition word_bytes : Z := 32.
	Definition word_limb_bytes : Z := 4.
	Definition word_limb_count : nat := 8.
	Definition native_stack_limit_words : Z := 1024.
	Definition frame_link_offset : Z := 0.
	Definition frame_ra_offset : Z := 8.
	Definition frame_stack_base : Z := 16.
	Definition frame_stack_bytes : Z := native_stack_limit_words * word_bytes.
	Definition frame_size : Z := frame_stack_base + frame_stack_bytes.

	Definition frame_link_ptrofs : ptrofs := Ptrofs.repr frame_link_offset.
	Definition frame_ra_ptrofs : ptrofs := Ptrofs.repr frame_ra_offset.

	Definition arg_in : ireg := RDI.
	Definition arg_insize : ireg := RSI.
	Definition arg_out : ireg := RDX.
	Definition arg_outsize : ireg := RCX.
	Definition stack_ptr_reg : ireg := R8.
	Definition tmp0 : ireg := R9.
	Definition tmp1 : ireg := R10.

	Definition as_int (z : Z) : int := Int.repr z.
	Definition as_int64 (z : Z) : int64 := Int64.repr z.

	Definition reg_addr (base : ireg) (ofs : Z) : addrmode :=
		Addrmode (Some base) None (inl _ ofs).

	Definition pc_label (pc : nat) : label := Pos.of_succ_nat pc.

	Definition label_span (p : Bytecode.program) : nat :=
		S (length (program_bytes p)).

	Definition local_label (p : Bytecode.program) (tag pc slot : nat) : label :=
		Pos.of_succ_nat
			(length (program_bytes p)
			+ tag * label_span p * label_span p
			+ pc * label_span p
			+ slot).

	Definition halt_label (p : Bytecode.program) : label := local_label p 1 0 0.
	Definition jump_zero_label (p : Bytecode.program) (pc : nat) : label :=
		local_label p 2 pc 0.
	Definition jump_case_label (p : Bytecode.program) (pc case_index : nat) : label :=
		local_label p 3 pc case_index.

	Definition limb_offset (limb : nat) : Z := word_limb_bytes * Z.of_nat limb.
	Definition internal_word_offset (word_index : nat) (limb : nat) : Z :=
		word_bytes * Z.of_nat word_index + limb_offset limb.

	Definition external_word_offset (word_index : nat) (limb : nat) : Z :=
		word_bytes * Z.of_nat word_index + word_limb_bytes * Z.of_nat (7 - limb).

	Definition frame_stack_end : Z := frame_stack_base + frame_stack_bytes.

	Definition word_limb (value : Z) (limb : nat) : Z :=
		Z.land (Z.shiftr value (32 * Z.of_nat limb)) (Z.ones 32).

	Definition word_limb_int (value : Z) (limb : nat) : int :=
		as_int (word_limb value limb).

	Definition all_limbs : list nat := seq 0 word_limb_count.

	Fixpoint compile_limb_code (f : nat -> code) (limbs : list nat) : code :=
		match limbs with
		| [] => []
		| limb :: rest => f limb ++ compile_limb_code f rest
		end.

	Definition jumpdest_pcs (p : Bytecode.program) : list nat :=
		fold_right
			(fun i acc =>
				match instr_opcode i with
				| OpJumpdest => instr_pc i :: acc
				| _ => acc
				end)
			[]
			(program_code p).

	Definition init_stack_pointer : code :=
		[Pleaq stack_ptr_reg (reg_addr RSP frame_stack_base)].

	Definition halt_if_stack_full (halt : label) : code :=
		[Pleaq tmp0 (reg_addr RSP frame_stack_end);
		Pcmpq_rr stack_ptr_reg tmp0;
		Pjcc Cond_ae halt].

	Definition halt_if_stack_below (required_bytes : Z) (halt : label) : code :=
		[Pleaq tmp0 (reg_addr RSP (frame_stack_base + required_bytes));
		Pcmpq_rr stack_ptr_reg tmp0;
		Pjcc Cond_b halt].

	Definition halt_if_input_oob (index : nat) (halt : label) : code :=
		[Pcmpq_ri arg_insize (as_int64 (Z.of_nat index));
		Pjcc Cond_be halt].

	Definition halt_if_output_oob (index : nat) (halt : label) : code :=
		[Pcmpq_ri arg_outsize (as_int64 (Z.of_nat index));
		Pjcc Cond_be halt].

	Definition load_external_word (src_base : ireg) (src_index : nat)
			(dst_base : ireg) (dst_word_index : nat) : code :=
		compile_limb_code
			(fun limb =>
				[Pmovl_rm tmp0 (reg_addr src_base (external_word_offset src_index limb));
					Pbswap32 tmp0;
					Pmovl_mr (reg_addr dst_base (internal_word_offset dst_word_index limb)) tmp0])
			all_limbs.

	Definition store_external_word (src_base : ireg) (src_word_index : nat)
			(dst_base : ireg) (dst_index : nat) : code :=
		compile_limb_code
			(fun limb =>
				[Pmovl_rm tmp0 (reg_addr src_base (internal_word_offset src_word_index limb));
					Pbswap32 tmp0;
					Pmovl_mr (reg_addr dst_base (external_word_offset dst_index limb)) tmp0])
			all_limbs.

	Definition store_external_word_from_offset (src_base : ireg) (src_ofs : Z)
			(dst_base : ireg) (dst_index : nat) : code :=
		compile_limb_code
			(fun limb =>
				[Pmovl_rm tmp0 (reg_addr src_base (src_ofs + limb_offset limb));
					Pbswap32 tmp0;
					Pmovl_mr (reg_addr dst_base (external_word_offset dst_index limb)) tmp0])
			all_limbs.

	Definition copy_internal_word (src_base : ireg) (src_word_index : nat)
			(dst_base : ireg) (dst_word_index : nat) : code :=
		compile_limb_code
			(fun limb =>
				[Pmovl_rm tmp0 (reg_addr src_base (internal_word_offset src_word_index limb));
					Pmovl_mr (reg_addr dst_base (internal_word_offset dst_word_index limb)) tmp0])
			all_limbs.

	Definition copy_internal_word_from_offset (src_base : ireg) (src_ofs : Z)
			(dst_base : ireg) (dst_word_index : nat) : code :=
		compile_limb_code
			(fun limb =>
				[Pmovl_rm tmp0 (reg_addr src_base (src_ofs + limb_offset limb));
					Pmovl_mr (reg_addr dst_base (internal_word_offset dst_word_index limb)) tmp0])
			all_limbs.

	Definition add_top_words : code :=
		[Pmovl_rm tmp0 (reg_addr stack_ptr_reg (-64));
		Pmovl_rm tmp1 (reg_addr stack_ptr_reg (-32));
		Paddl_rr tmp0 tmp1;
		Pmovl_mr (reg_addr stack_ptr_reg (-64)) tmp0]
		++ compile_limb_code
				(fun limb =>
						[Pmovl_rm tmp0
							(reg_addr stack_ptr_reg (-64 + limb_offset (S limb)));
						Pmovl_rm tmp1
							(reg_addr stack_ptr_reg (-32 + limb_offset (S limb)));
						Padcl_rr tmp0 tmp1;
						Pmovl_mr
							(reg_addr stack_ptr_reg (-64 + limb_offset (S limb))) tmp0])
				(seq 0 7)
		++ [Psubq_ri stack_ptr_reg (as_int64 word_bytes)].

	Definition sub_top_words : code :=
		[Pmovl_rm tmp0 (reg_addr stack_ptr_reg (-64));
		Pmovl_rm tmp1 (reg_addr stack_ptr_reg (-32));
		Psubl_rr tmp0 tmp1;
		Pmovl_mr (reg_addr stack_ptr_reg (-64)) tmp0]
		++ compile_limb_code
				(fun limb =>
						[Pmovl_rm tmp0
							(reg_addr stack_ptr_reg (-64 + limb_offset (S limb)));
						Pmovl_rm tmp1
							(reg_addr stack_ptr_reg (-32 + limb_offset (S limb)));
						Psbbl_rr tmp0 tmp1;
						Pmovl_mr
							(reg_addr stack_ptr_reg (-64 + limb_offset (S limb))) tmp0])
				(seq 0 7)
		++ [Psubq_ri stack_ptr_reg (as_int64 word_bytes)].

	Definition zero_test_word_at (base : ireg) (ofs : Z) (on_zero : label) : code :=
		[Pxorl_r tmp0]
		++ compile_limb_code
				(fun limb =>
						[Pmovl_rm tmp1 (reg_addr base (ofs + limb_offset limb));
						Porl_rr tmp0 tmp1])
				all_limbs
		++ [Ptestl_rr tmp0 tmp0;
				Pjcc Cond_e on_zero].

	Definition compare_word_at_with (base : ireg) (ofs value : Z)
			(on_mismatch : label) : code :=
		compile_limb_code
			(fun limb =>
				[Pmovl_rm tmp0 (reg_addr base (ofs + limb_offset limb));
					Pcmpl_ri tmp0 (word_limb_int value limb);
					Pjcc Cond_ne on_mismatch])
			all_limbs.

	Fixpoint compile_jump_cases (p : Bytecode.program) (pc : nat)
		(case_index : nat)
			(destinations : list nat) : code :=
		match destinations with
		| [] => [Pjmp_l (halt_label p)]
		| destination :: rest =>
				let miss := jump_case_label p pc case_index in
				compare_word_at_with stack_ptr_reg word_bytes (Z.of_nat destination) miss
				++ [Pjmp_l (pc_label destination); Plabel miss]
				++ compile_jump_cases p pc (S case_index) rest
		end.

	Definition compile_push_from_input (p : Bytecode.program) (index : nat) : code :=
		halt_if_input_oob index (halt_label p)
		++ halt_if_stack_full (halt_label p)
		++ load_external_word arg_in index stack_ptr_reg 0
		++ [Paddq_ri stack_ptr_reg (as_int64 word_bytes)].

	Definition compile_store_to_output (p : Bytecode.program) (index : nat) : code :=
		halt_if_output_oob index (halt_label p)
		++ halt_if_stack_below word_bytes (halt_label p)
		++ store_external_word_from_offset stack_ptr_reg (- word_bytes) arg_out index
		++ [Psubq_ri stack_ptr_reg (as_int64 word_bytes)].

	Definition compile_dup (p : Bytecode.program) : code :=
		halt_if_stack_below word_bytes (halt_label p)
		++ halt_if_stack_full (halt_label p)
		++ copy_internal_word_from_offset stack_ptr_reg (- word_bytes) stack_ptr_reg 0
		++ [Paddq_ri stack_ptr_reg (as_int64 word_bytes)].

	Definition compile_jumpi (p : Bytecode.program) (pc : nat) : code :=
		halt_if_stack_below (2 * word_bytes) (halt_label p)
		++ zero_test_word_at stack_ptr_reg (-64) (jump_zero_label p pc)
		++ [Psubq_ri stack_ptr_reg (as_int64 (2 * word_bytes))]
		++ compile_jump_cases p pc 0 (jumpdest_pcs p)
		++ [Plabel (jump_zero_label p pc);
				Psubq_ri stack_ptr_reg (as_int64 (2 * word_bytes))].

	Definition transl_instruction (p : Bytecode.program)
		(i : Bytecode.instruction) : code :=
		match instr_opcode i with
		| OpStop => [Pjmp_l (halt_label p)]
		| OpLoad index => compile_push_from_input p index
		| OpStore index => compile_store_to_output p index
		| OpPop =>
				halt_if_stack_below word_bytes (halt_label p)
				++ [Psubq_ri stack_ptr_reg (as_int64 word_bytes)]
		| OpAdd =>
				halt_if_stack_below (2 * word_bytes) (halt_label p)
				++ add_top_words
		| OpSub =>
				halt_if_stack_below (2 * word_bytes) (halt_label p)
				++ sub_top_words
		| OpDup => compile_dup p
		| OpJumpdest => []
		| OpJumpi => compile_jumpi p (instr_pc i)
		end.

	Definition transl_labeled_instruction (p : Bytecode.program)
			(i : Bytecode.instruction) : code :=
		Plabel (pc_label (instr_pc i)) :: transl_instruction p i.

	Fixpoint transl_code (p : Bytecode.program)
			(code0 : list Bytecode.instruction) : code :=
		match code0 with
		| [] => []
		| i :: rest => transl_labeled_instruction p i ++ transl_code p rest
		end.

	Definition transl_program_code (p : Bytecode.program) : code :=
		[Pallocframe frame_size frame_ra_ptrofs frame_link_ptrofs]
		++ init_stack_pointer
		++ transl_code p (program_code p)
		++ [Plabel (halt_label p);
				Pfreeframe frame_size frame_ra_ptrofs frame_link_ptrofs;
				Pret].

	Definition transl_program (p : Bytecode.program) : function :=
		mkfunction bytecode_signature (transl_program_code p).

	Definition transl_bytes (bytes : list Bytecode.byte)
			: Bytecode.parse_result function :=
		match Bytecode.parse bytes with
		| Bytecode.Parsed p => Bytecode.Parsed (transl_program p)
		| Bytecode.Rejected error => Bytecode.Rejected error
		end.


End Comp.

Section Example.

	Definition example_byte (z : Z) : Bytecode.Byte.t :=
		Bytecode.Byte.repr z.

	Definition add_store_bytes : list Bytecode.byte :=
		[example_byte 1; example_byte 0;
		example_byte 1; example_byte 1;
		example_byte 4;
		example_byte 2; example_byte 0;
		example_byte 0].

	Definition add_store_program : Bytecode.program :=
		{| program_bytes := add_store_bytes;
			program_code :=
				[make_instruction 0 (OpLoad 0);
				 make_instruction 2 (OpLoad 1);
				 make_instruction 4 OpAdd;
				 make_instruction 5 (OpStore 0);
				 make_instruction 7 OpStop] |}.

	Eval compute in parse add_store_bytes.
	
	Definition add_store_function : function :=
		transl_program add_store_program.

	Definition add_store_code : code :=
		fn_code add_store_function.

	Definition add_store_translation : Bytecode.parse_result function :=
		transl_bytes add_store_bytes.

	Definition add_store_translation_matches :
		add_store_translation = Bytecode.Parsed add_store_function.
	Proof.
		reflexivity.
	Qed.

	Definition add_store_code_size : nat :=
		length add_store_code.

	Definition add_store_initial_state : source_state :=
		{| source_pc := 0;
			source_stack := [];
			source_inputs := [41; 1];
			source_outputs := [0] |}.

	Definition add_store_initial_config : configuration :=
		Running add_store_initial_state.

		
	Eval compute in run 5 add_store_program add_store_initial_config.

	Eval compute in
		match parse add_store_bytes with
		| Parsed p => run 5 p add_store_initial_config
		| Rejected err => add_store_initial_config
		end.

	Definition truncated_load_bytes : list Bytecode.byte :=
		[example_byte 1].

	Definition truncated_load_translation : Bytecode.parse_result function :=
		transl_bytes truncated_load_bytes.

	Definition truncated_load_is_rejected : 
		truncated_load_translation = Bytecode.Rejected (TruncatedOperand 0).
	Proof. reflexivity. Qed.

End Example.



