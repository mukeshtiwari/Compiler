From Bytecode Require Import Bytecode.
From Assembly Require Import Assembly.
From Proofs Require Import Proof.
From compcert.common Require Import AST.
From compcert.common Require Import Values Memory Globalenvs Events.
From compcert.lib Require Import Integers.
From compcert.x86 Require Import Asm.
From Stdlib Require Import List ZArith PeanoNat
Relation_Operators Utf8.

Import ListNotations.

Section GenericCorrectnessStatements.

  (** Statement-only file for generic compiler correctness.
      This file intentionally contains no Rocq proof terms.

        
    
  *)

  

  Variables
    (initial_target_state : function -> list word -> list word -> Asm.state)
    (target_outputs : Asm.state -> list word)
    (target_star : Asm.state -> Asm.state -> Prop)
    (target_final : Asm.state -> Prop).
 
  (** This theorem states that for any parsed bytecode program [p],
      any source configuration [cfg], and any amount of fuel [fuel],
      if the source machine runs for [fuel] steps and ends in [cfg'],
      then the compiled x86‑64 code, started with the input and output
      vectors extracted from [cfg], will simulate that execution
      (in zero or more target steps) to some target state [t'] whose
      output vector equals the source's final output vector.
    *)
  Theorem compiler_correct
    (bytes : list Bytecode.byte) (fuel : nat)
    (p : Bytecode.program) (cfg cfg' : configuration) : 
    Bytecode.parse bytes = Bytecode.Parsed p ->
    run fuel p cfg = cfg' ->
    exists (t' : Asm.state),
      target_star (initial_target_state (transl_program p)
        (source_inputs (configuration_to_state cfg))
        (source_outputs (configuration_to_state cfg))) t' /\
      target_outputs t' = source_outputs (configuration_to_state cfg').
  Proof. Admitted.

End GenericCorrectnessStatements.
