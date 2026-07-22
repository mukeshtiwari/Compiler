From Bytecode Require Import Bytecode.
From Assembly Require Import Assembly.
From compcert.x86 Require Import Asm.
From compcert.common Require Import AST.

Require Extraction.

Extraction Language OCaml.
Set Extraction Output Directory ".".

(* Extract only the compiler entrypoint and the target Asm function view it returns. *)
Extraction "compiler_extracted.ml"
  transl_bytes
  Asm.function
  Asm.code
  Asm.instruction
  Asm.addrmode
  Asm.ireg
  Asm.testcond.
