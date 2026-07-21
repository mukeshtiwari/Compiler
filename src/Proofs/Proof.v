From Bytecode Require Import Bytecode.
From Assembly Require Import Assembly.
From compcert.common Require Import Values Memory.
From compcert.lib Require Import Integers.
From compcert.x86 Require Import Asm.
From Stdlib Require Import List ZArith 
Relation_Operators Utf8.

Import ListNotations.

Section CorrectnessSkeleton.

(* Concrete CompCert x86 machine state used as the target semantics state. *)
Definition target_state : Type := Asm.state.

(* Fixed target environment components used to build initial machine states. *)
Variable code_block : block.
Variable input_block : block.
Variable output_block : block.
Variable initial_mem : mem.
Variable ge : genv.

(* Initial x86 state built from compiled code and concrete input/output words. *)
Definition initial_target_state
	(_ : function) (inputs outputs : list word) : target_state :=
	let rs0 :=
		Pregmap.set PC (Vptr code_block Ptrofs.zero)
			(Pregmap.set RA Vnullptr
				(Pregmap.set RSP Vnullptr
					(Pregmap.set RDI (Vptr input_block Ptrofs.zero)
						(Pregmap.set RSI (Vint (Int.repr (Z.of_nat (length inputs))))
							(Pregmap.set RDX (Vptr output_block Ptrofs.zero)
								(Pregmap.set RCX (Vint (Int.repr (Z.of_nat (length outputs))))
									(Pregmap.init Values.Vundef))))))) in
	State rs0 initial_mem.

(* One small-step transition of the target machine semantics. *)
Definition target_step (s1 s2 : target_state) : Prop :=
	exists t, step ge s1 t s2.

(* Reflexive-transitive closure of target transitions (zero or more steps). *)
Definition target_star : target_state -> target_state -> Prop :=
	clos_refl_trans target_state target_step.

(* Predicate identifying target states where execution has halted/returned. *)
Definition target_final (st : target_state) : Prop :=
	match st with
	| State rs _ => rs#PC = Vnullptr
	end.

(* Observable output vector extracted from a target state. *)
Variable target_outputs : target_state -> list word.

(* Simulation invariant relating one source configuration to one target state. *)
Variable match_config :
	Bytecode.program -> configuration -> target_state -> Prop.

(* Source-side initial configuration from concrete input/output vectors. *)
Definition source_initial_config (inputs outputs : list word) : configuration :=
	Running
		{| source_pc := 0;
			 source_stack := [];
			 source_inputs := inputs;
			 source_outputs := outputs |}.

(* The compiler always emits a function with the expected C-facing signature. *)
Theorem transl_program_has_expected_signature :
	forall p,
		fn_sig (transl_program p) = bytecode_signature.
Proof.
 intro p; reflexivity.
Qed.

(* Parse failures are preserved exactly by the top-level compiler entry. *)
Theorem transl_bytes_rejects_exactly_parse_errors :
	forall bytes err,
		Bytecode.parse bytes = Bytecode.Rejected err ->
		transl_bytes bytes = Bytecode.Rejected err.
Proof.
Admitted.

(* Parse success compiles to the same function as direct program translation. *)
Theorem transl_bytes_parsed_is_transl_program :
	forall bytes p,
		Bytecode.parse bytes = Bytecode.Parsed p ->
		transl_bytes bytes = Bytecode.Parsed (transl_program p).
Proof.
Admitted.

(* Initial source and target states satisfy the simulation invariant. *)
Theorem match_initial_states :
	forall p inputs outputs,
		match_config
			p
			(source_initial_config inputs outputs)
			(initial_target_state (transl_program p) inputs outputs).
Proof.
Admitted.

(* Each source small step is simulated by zero or more target steps. *)
Theorem source_step_simulated_by_target_star :
	forall p c1 c2 t1,
		source_small_step p c1 c2 ->
		match_config p c1 t1 ->
		exists t2,
			target_star t1 t2 /\ match_config p c2 t2.
Proof.
Admitted.

(* Once the source has halted, the target can also reach a final state. *)
Theorem source_halt_implies_target_can_halt :
	forall p reason st t,
		match_config p (Halted reason st) t ->
		exists t',
			target_star t t' /\ target_final t'.
Proof.
Admitted.

(* Fuel-bounded source execution is simulated by target multi-step execution. *)
Theorem run_fuel_simulation :
	forall fuel p c t,
		match_config p c t ->
		exists t',
			target_star t t' /\ match_config p (run fuel p c) t'.
Proof.
Admitted.

(* For halted runs, the observable outputs of source and target coincide. *)
Theorem run_fuel_outputs_agree_when_halted :
	forall fuel p c reason st t t',
		match_config p c t ->
		run fuel p c = Halted reason st ->
		target_star t t' ->
		match_config p (Halted reason st) t' ->
		target_outputs t' = source_outputs st.
Proof.
Admitted.

(* End-to-end theorem from bytes: parse, compile, then simulate source run. *)
Theorem end_to_end_bytes_correctness :
	forall fuel bytes p inputs outputs,
		Bytecode.parse bytes = Bytecode.Parsed p ->
		exists t',
			target_star
				(initial_target_state (transl_program p) inputs outputs)
				t' ∧
			match_config p (run fuel p (source_initial_config inputs outputs)) t'.
Proof.
Admitted.

End CorrectnessSkeleton.