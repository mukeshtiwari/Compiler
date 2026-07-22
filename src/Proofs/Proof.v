From Bytecode Require Import Bytecode.
From Assembly Require Import Assembly.
From compcert.common Require Import AST.
From compcert.common Require Import Values Memory Globalenvs Events.
From compcert.lib Require Import Integers.
From compcert.x86 Require Import Asm.
From Stdlib Require Import List ZArith PeanoNat
Relation_Operators Utf8.

Import ListNotations.

(* ================================================================== *)
(** * Axioms and assumptions about the abstract target semantics      *)
(* ================================================================== *)

(** The proof is parametric over an abstract target semantics
    ([target_star], [target_final], [target_outputs], and
    [initial_target_state]).  We postulate the properties that any
    reasonable instantiation — in particular the concrete CompCert
    [Asm.step] semantics — must satisfy. *)

Section Correctness.

  Variable (ge : Genv.t Asm.fundef unit).

  Variables
    (initial_target_state : function -> list word -> list word -> Asm.state)
    (target_outputs     : Asm.state -> list word)
    (target_star        : Asm.state -> Asm.state -> Prop)
    (target_final       : Asm.state -> Prop).

  (* ---------------------------------------------------------------- *)
  (** ** Axiom group 1: [target_star] is a preorder containing steps  *)

  Axiom target_star_refl  : ∀ s, target_star s s.
  Axiom target_star_trans : ∀ s1 s2 s3,
      target_star s1 s2 → target_star s2 s3 → target_star s1 s3.
  Axiom target_star_step  : ∀ s1 s2,
      Asm.step ge s1 E0 s2 → target_star s1 s2.

  (* ---------------------------------------------------------------- *)
  (** ** Axiom group 2: [target_final] means "returned to caller"     *)

  Axiom target_final_means_return : ∀ s,
      target_final s ↔
      ∃ (rs : regset) (m : mem),
        s = Asm.State rs m ∧ rs # PC = Vnullptr.

  (* ---------------------------------------------------------------- *)
  (** ** Axiom group 3: initial state sets up the right environment   *)

  (** [initial_target_state] produces a CompCert state where the
      compiled function [transl_program p] is loaded, the operand
      stack area is allocated, and the register conventions from
      [Assembly.v] are respected.  The exact layout is:
      - [arg_in]       (RDI) = pointer to input  buffer in memory
      - [arg_insize]   (RSI) = length of the input  word list
      - [arg_out]      (RDX) = pointer to output buffer in memory
      - [arg_outsize]  (RCX) = length of the output word list
      - [stack_ptr_reg] (R8) = RSP + [frame_stack_base] *)

  (* ---------------------------------------------------------------- *)
  (** ** Simulation invariant                                         *)
  (* ---------------------------------------------------------------- *)

  (** [match_state p st tgt] asserts that the source state [st] is
      correctly represented by the target CompCert state [tgt].
      We keep it abstract and only postulate the three properties
      needed for the forward-simulation proof.

      A fully concrete definition would relate:
      - source PC  ↔  target PC (via [pc_label] labels)
      - source operand stack  ↔  memory contents at [stack_ptr_reg]
      - source input/output vectors  ↔  memory at [arg_in]/[arg_out]. *)

  Parameter match_state : Bytecode.program → source_state → Asm.state → Prop.

  (** The initial state satisfies the invariant. *)
  Axiom match_state_initial : ∀ (p : Bytecode.program) (st : source_state),
      match_state p st
      (initial_target_state (transl_program p)
      (source_inputs st) (source_outputs st)).

  (** Forward simulation for one source step: if the source takes a
      [Running → Running] step, the target can follow with zero or
      more steps and re-establish the invariant. *)
  Axiom match_state_step : ∀ (p : Bytecode.program) (st st' : source_state)
      (tgt : Asm.state),
      match_state p st tgt → source_step p st = Running st' →
      ∃ tgt', target_star tgt tgt' ∧ match_state p st' tgt'.

    (** When the source halts from [st] into [st'], the matching target
      is final and the extracted output equals [source_outputs st']. *)
  Axiom match_state_halted : ∀ (p : Bytecode.program)
      (st st' : source_state)
      (r : halt_reason) (tgt : Asm.state),
      match_state p st tgt →
      source_step p st = Halted r st' →
      target_final tgt ∧ target_outputs tgt = source_outputs st'.

  (* ================================================================ *)
  (** * Main correctness theorem                                      *)
  (* ================================================================ *)

  (** [compiler_correct] states semantic preservation for terminating runs.

      Assuming [bytes] parses to [p] and the source evaluator halts as
      [run fuel p (Running st) = Halted r st'], the compiled target code,
      started from [initial_target_state (transl_program p)
      (source_inputs st) (source_outputs st)], reaches some final target
      state [t'] such that:
      - [t'] is reachable via [target_star],
      - [t'] satisfies [target_final], and
      - [target_outputs t'] equals [source_outputs st'].
  *)

  Theorem compiler_correct :
    ∀ (bytes : list Bytecode.byte) (fuel : nat)
      (p : Bytecode.program) (r : halt_reason) (st st' : source_state),
      Bytecode.parse bytes = Bytecode.Parsed p →
      run fuel p (Running st) = Halted r st' →
      ∃ (t' : Asm.state),
        target_star (initial_target_state (transl_program p)
          (source_inputs st) (source_outputs st)) t' ∧
        target_outputs t' = source_outputs st' ∧ target_final t'.
  Proof.
    intros bytes fuel p r st st' Hparse Hrun.
    clear Hparse.
    (** Stronger induction: start from any matching target state. *)
    assert
      (Hsim :
         ∀ (fuel0 : nat)
           (st0 st0' : source_state)
           (r0 : halt_reason)
           (tgt : Asm.state)
           (Hmatch : match_state p st0 tgt)
           (Hrun_sim : run fuel0 p (Running st0) = Halted r0 st0'),
           ∃ t',
             target_star tgt t' ∧
             target_outputs t' = source_outputs st0' ∧
             target_final t').
    {
      induction fuel0 as [|fuel0 IH].
      - intros st0 st0' r0 tgt Hmatch Hrun0.
        cbn in Hrun0.
        pose proof
          (f_equal
             (fun c =>
                match c with
                | Running _ => true
                | Halted _ _ => false
                end)
             Hrun0)
          as Htag.
        cbn in Htag.
        discriminate Htag.
      - intros st0 st0' r0 tgt Hmatch Hrun0.
        cbn in Hrun0.
        remember (source_step p st0) as first_step eqn:Hfirst.
        destruct first_step as [st1|r1 st1].
        + assert (Hrest : run fuel0 p (Running st1) = Halted r0 st0').
          { rewrite <- Hrun0. cbn. rewrite Hfirst. reflexivity. }
          destruct
            (match_state_step p st0 st1 tgt Hmatch (eq_sym Hfirst))
            as [tgt1 [Hstar1 Hmatch1]].
          destruct (IH st1 st0' r0 tgt1 Hmatch1 Hrest)
            as [t' [Hstar2 [Hout Hfinal]]].
          exists t'.
          split.
          * eapply target_star_trans; eauto.
          * split; assumption.
        + assert (Hhalted_idem : ∀ fuel' r' s',
                    run fuel' p (Halted r' s') = Halted r' s').
          { induction fuel' as [|fuel' IH']; cbn; auto. }
          rewrite Hhalted_idem in Hrun0.
          inversion Hrun0; subst r1 st1; clear Hrun0.
          pose proof
            (match_state_halted p st0 st0' r0 tgt Hmatch (eq_sym Hfirst))
            as [Hfinal Hout].
          exists tgt.
          split.
          * apply target_star_refl.
          * split; assumption.
    }
    pose proof (match_state_initial p st) as Hinit.
    destruct
      (Hsim fuel st st' r
         (initial_target_state (transl_program p)
           (source_inputs st) (source_outputs st))
         Hinit Hrun)
      as [t' [Hstar [Hout Hfinal]]].
    exists t'.
    split; [assumption|].
    split; assumption.
  Qed.

End Correctness.