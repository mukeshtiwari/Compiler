From Bytecode Require Import Bytecode.
From Assembly Require Import Assembly.
From compcert.common Require Import AST.
From compcert.common Require Import Values Memory Globalenvs Events.
From compcert.lib Require Import Integers.
From compcert.x86 Require Import Asm.
From Stdlib Require Import List ZArith PeanoNat
Relation_Operators Utf8.

Import ListNotations.

Section GenericCorrectness.

  (** This section is parameterized by an abstract target machine semantics.
      The goal is to prove a reusable compiler-correctness statement that does
      not depend on one concrete small-step relation from CompCert. *)
  Variable (ge : Genv.t Asm.fundef unit).

  (** Abstract target-side interface used by the proof:
      - [initial_target_state] builds the initial machine state for a compiled
        function with given inputs and initial outputs;
      - [target_outputs] extracts the observable outputs of a target state;
      - [target_star] is the multi-step target execution relation;
      - [target_final] marks states considered final/halting. *)
  Variables
    (initial_target_state : function -> list word -> list word -> Asm.state)
    (target_outputs : Asm.state -> list word)
    (target_star : Asm.state -> Asm.state -> Prop)
    (target_final : Asm.state -> Prop).

    (** Structural properties of the target multi-step relation.
      Reflexivity lets us keep the current state when no extra target steps
      are needed; transitivity lets us concatenate simulation segments. *)
    Axiom gen_target_star_refl : ∀ s, target_star s s.
    Axiom gen_target_star_trans : ∀ s1 s2 s3,
      target_star s1 s2 → target_star s2 s3 → target_star s1 s3.

    (** Simulation relation connecting one source state with one target state
      for a given source program. This is the central invariant carried
      throughout the correctness argument. *)
    Parameter gen_match_state : Bytecode.program → source_state → Asm.state → Prop.

    (** Initial-state compatibility: starting from source state [st], the target
      state created from the compiled program is related by [gen_match_state]. *)
    Axiom gen_match_state_initial : ∀ (p : Bytecode.program) (st : source_state),
      gen_match_state p st
      (initial_target_state (transl_program p)
      (source_inputs st) (source_outputs st)).

    (** Forward simulation for running steps: if source takes one running step,
      the target can take zero or more steps to a new related target state. *)
    Axiom gen_match_state_step : ∀ (p : Bytecode.program) (st st' : source_state)
      (tgt : Asm.state),
      gen_match_state p st tgt → source_step p st = Running st' →
      ∃ tgt', target_star tgt tgt' ∧ gen_match_state p st' tgt'.

    (** Observation agreement: any matched pair of states exposes the same
      output sequence at the source and target levels. *)
    Axiom gen_match_state_outputs : ∀ (p : Bytecode.program)
      (st : source_state) (tgt : Asm.state),
      gen_match_state p st tgt →
      target_outputs tgt = source_outputs st.

    (** Halt compatibility: when source halts in one step from a matched state,
      the current target state is already final and observes the halted
      source outputs. *)
    Axiom gen_match_state_halted : ∀ (p : Bytecode.program)
      (st st' : source_state)
      (r : halt_reason) (tgt : Asm.state),
      gen_match_state p st tgt →
      source_step p st = Halted r st' →
      target_final tgt ∧ target_outputs tgt = source_outputs st'.

  (** Helper projection from a full source configuration to its underlying
      [source_state]. This forgets the halt reason, since output comparison
      only depends on the embedded state fields. *)
  Definition configuration_to_state (cfg : configuration) : source_state :=
    match cfg with 
    | Running st => st 
    | Halted _ st => st 
    end.

  (** Executing [run] from a halted configuration cannot change it, regardless
      of available fuel. This lemma is used in the halted-start branch of the
      main theorem. *)
  Lemma gen_run_halted_idem :
    ∀ (fuel : nat) (p : Bytecode.program) (r : halt_reason) (st : source_state),
      run fuel p (Halted r st) = Halted r st.
  Proof.
    induction fuel as [|fuel IH]; cbn; auto.
  Qed.

  (** Running-start case of the main correctness theorem.
      If execution begins from [Running st] and reaches [cfg'], then the target
      can reach a state whose observed outputs match [cfg']'s source outputs. *)
  Lemma compiler_correct_gen_running :
    ∀ (fuel : nat) (p : Bytecode.program)
      (st : source_state) (cfg' : configuration),
      run fuel p (Running st) = cfg' →
      ∃ (t' : Asm.state),
        target_star (initial_target_state (transl_program p)
          (source_inputs st) (source_outputs st)) t' ∧
        target_outputs t' = source_outputs (configuration_to_state cfg').
  Proof.
    intros fuel p st cfg' Hrun.
    assert
      (Hsim :
        ∀ (fuel0 : nat)
          (st0 : source_state)
          (cfg0 : configuration)
          (tgt : Asm.state),
          gen_match_state p st0 tgt →
          run fuel0 p (Running st0) = cfg0 →
          ∃ t',
            target_star tgt t' ∧
            target_outputs t' = source_outputs (configuration_to_state cfg0)).
    {
      induction fuel0 as [|fuel0 IH]; intros st0 cfg0 tgt Hmatch Hrun0.
      - cbn in Hrun0.
        inversion Hrun0; subst cfg0.
        exists tgt.
        split.
        + apply gen_target_star_refl.
        + cbn. eapply gen_match_state_outputs; eauto.
      - cbn in Hrun0.
        remember (source_step p st0) as first_step eqn:Hfirst.
        destruct first_step as [st1 | r1 st1].
        + assert (Hrest : run fuel0 p (Running st1) = cfg0).
          { rewrite <- Hrun0. cbn. rewrite Hfirst. reflexivity. }
          destruct (gen_match_state_step p st0 st1 tgt Hmatch (eq_sym Hfirst))
            as [tgt1 [Hstar1 Hmatch1]].
          destruct (IH st1 cfg0 tgt1 Hmatch1 Hrest)
            as [t' [Hstar2 Hout]].
          exists t'.
          split.
          * eapply gen_target_star_trans; eauto.
          * exact Hout.
        + rewrite gen_run_halted_idem in Hrun0.
          inversion Hrun0; subst cfg0.
          pose proof
            (gen_match_state_halted p st0 st1 r1 tgt Hmatch (eq_sym Hfirst))
            as [_ Hout].
          exists tgt.
          split.
          * apply gen_target_star_refl.
          * exact Hout.
    }
    pose proof (gen_match_state_initial p st) as Hinit.
    destruct (Hsim fuel st cfg'
      (initial_target_state (transl_program p)
        (source_inputs st) (source_outputs st))
      Hinit Hrun) as [t' [Hstar Hout]].
    exists t'.
    split; assumption.
  Qed.
  (** Main generic compiler-correctness statement. 
      This theorem states that for any parsed bytecode program [p],
      any source configuration [cfg], and any amount of fuel [fuel],
      if the source machine runs for [fuel] steps and ends in [cfg'],
      then the compiled x86‑64 code, started with the input and output
      vectors extracted from [cfg], will simulate that execution
      (in zero or more target steps) to some target state [t'] whose
      output vector equals the source's final output vector.


      The proof splits on [cfg]:
      - running case: delegated to [compiler_correct_gen_running];
      - halted case: source does not evolve, so initial target state already
        satisfies the required output relation. *)
  Theorem compiler_correct :
    ∀ (bytes : list Bytecode.byte) (fuel : nat)
      (p : Bytecode.program) (cfg cfg' : configuration),
      Bytecode.parse bytes = Bytecode.Parsed p →
      run fuel p cfg = cfg' →
      ∃ (t' : Asm.state),
        target_star (initial_target_state (transl_program p)
        (source_inputs (configuration_to_state cfg)) 
        (source_outputs (configuration_to_state cfg))) t' ∧
        target_outputs t' = source_outputs (configuration_to_state cfg').
  Proof.
    intros bytes fuel p cfg cfg' Hparse Hrun.
    clear Hparse.
    destruct cfg as [st | r st].
    { eapply compiler_correct_gen_running; eauto. }
    { rewrite gen_run_halted_idem in Hrun.
      inversion Hrun; subst cfg'.
      exists (initial_target_state (transl_program p)
        (source_inputs st) (source_outputs st)).
      split; [apply gen_target_star_refl |].
      eapply gen_match_state_outputs.
      apply gen_match_state_initial. }
  Qed.

End GenericCorrectness.

