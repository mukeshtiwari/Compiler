From Bytecode Require Import Bytecode.
From Assembly Require Import Assembly.

(* 
High level proof idea: For any bytecode program, running my compiled x86 
code on input (in, insize, out, outsize) produces the same final memory 
state as the formal Bytecode.v evaluator, or halts if the bytecode 
halts/faults

∀ p bytes in out, parse bytes = Parsed p → exec_x86 (compile p) in out = run fuel p (initial_state)

*)