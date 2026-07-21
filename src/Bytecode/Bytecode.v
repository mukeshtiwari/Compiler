(** * The compiler problem: source bytecode and its semantics

    A compiler input is a list of bytes.  Parsing turns it into a list of
    instructions whose program counters are byte offsets.  Execution uses a
    stack of 256-bit words, a read-only input vector, and a mutable output
    vector.  This file contains only those definitions; it mentions neither
    x86 nor target memory.

    The byte encoding is:

    - [00] STOP
    - [01 nn] LOAD input [nn]
    - [02 nn] STORE output [nn]
    - [03] POP
    - [04] ADD
    - [05] SUB
    - [06] DUP
    - [07] JUMPDEST
    - [08] JUMPI

    LOAD and STORE operands are unsigned one-byte word indices.  Their bounds
    are checked at execution time against the lengths of the input and output
    vectors.  An out-of-bounds access halts before changing the operand stack.
    Words are integers normalized modulo [2^256], and the stack limit is 1024
    words.

    The source model stores words as mathematical integers.  The assignment's
    C interface separately specifies that each vector element occupies 32
    bytes in big-endian order and that [insize] and [outsize] count words, not
    bytes. *)

From Stdlib Require Import ZArith List Bool Lia Logic.ProofIrrelevance.

Import ListNotations.
Open Scope Z_scope.

(** ** Syntax and parsing *)

(** Raw source syntax uses an intrinsically bounded byte.  This definition is
    part of the bytecode language; it is independent of both Jasmin words and
    the target machine's memory representation. *)
Module Byte.
  Record t : Type := {
    unsigned : Z;
    unsigned_range : 0 <= unsigned < 256
  }.

  Definition modulus : Z := 256.
  Definition max_unsigned : Z := 255.

  Definition repr (value : Z) : t.
  Proof.
    refine {| unsigned := value mod modulus |}.
    unfold modulus. apply Z.mod_pos_bound. lia.
  Defined.

  Lemma unsigned_repr :
    forall value,
      0 <= value <= max_unsigned ->
      unsigned (repr value) = value.
  Proof.
    intros value Hrange.
    change (value mod 256 = value).
    apply Z.mod_small. unfold max_unsigned in Hrange. lia.
  Qed.

  Lemma eq :
    forall left right,
      unsigned left = unsigned right ->
      left = right.
  Proof.
    intros [left Hleft] [right Hright] Hequal; cbn in Hequal; subst.
    f_equal. apply proof_irrelevance.
  Qed.

  Lemma repr_unsigned :
    forall value, repr (unsigned value) = value.
  Proof.
    intros value. apply eq. cbn.
    apply Z.mod_small. unfold modulus.
    pose proof (unsigned_range value). lia.
  Qed.
End Byte.

Notation byte := Byte.t.

Definition byte_nat (b : byte) : nat := Z.to_nat (Byte.unsigned b).

Inductive opcode : Type :=
  | OpStop
  | OpLoad (index : nat)
  | OpStore (index : nat)
  | OpPop
  | OpAdd
  | OpSub
  | OpDup
  | OpJumpdest
  | OpJumpi.

Definition opcode_width (op : opcode) : nat :=
  match op with
  | OpLoad _ | OpStore _ => 2
  | _ => 1
  end.

Record instruction : Type := {
  instr_pc : nat;
  instr_opcode : opcode;
  instr_next : nat
}.

Definition make_instruction (pc : nat) (op : opcode) : instruction :=
  {| instr_pc := pc;
     instr_opcode := op;
     instr_next := (pc + opcode_width op)%nat |}.

Inductive parse_error : Type :=
  | UnknownOpcode (pc raw : nat)
  | TruncatedOperand (pc : nat).

Inductive parse_result (A : Type) : Type :=
  | Parsed (value : A)
  | Rejected (error : parse_error).

Arguments Parsed {A} _.
Arguments Rejected {A} _.

Definition prepend_instruction
    (i : instruction) (result : parse_result (list instruction))
    : parse_result (list instruction) :=
  match result with
  | Parsed code => Parsed (i :: code)
  | Rejected error => Rejected error
  end.

Inductive operand_kind : Type := LoadOperand | StoreOperand.

(** [ExpectOperand pc kind] records an opcode whose operand byte has not yet
    been consumed.  Scanning one byte at a time keeps [scan] structurally
    recursive and makes a missing operand an explicit parse error. *)
Inductive scan_mode : Type :=
  | ExpectOpcode (pc : nat)
  | ExpectOperand (pc : nat) (kind : operand_kind).

Definition mode_pc (mode : scan_mode) : nat :=
  match mode with
  | ExpectOpcode pc | ExpectOperand pc _ => pc
  end.

Definition consumed_opcode_bytes (mode : scan_mode) : nat :=
  match mode with
  | ExpectOpcode _ => 0
  | ExpectOperand _ _ => 1
  end.

Fixpoint scan (mode : scan_mode) (bytes : list byte)
    : parse_result (list instruction) :=
  match mode, bytes with
  | ExpectOpcode _, [] => Parsed []
  | ExpectOperand pc _, [] => Rejected (TruncatedOperand pc)
  | ExpectOpcode pc, opbyte :: tail =>
      match byte_nat opbyte with
      | 0%nat => prepend_instruction (make_instruction pc OpStop)
                   (scan (ExpectOpcode (S pc)) tail)
      | 1%nat => scan (ExpectOperand pc LoadOperand) tail
      | 2%nat => scan (ExpectOperand pc StoreOperand) tail
      | 3%nat => prepend_instruction (make_instruction pc OpPop)
                   (scan (ExpectOpcode (S pc)) tail)
      | 4%nat => prepend_instruction (make_instruction pc OpAdd)
                   (scan (ExpectOpcode (S pc)) tail)
      | 5%nat => prepend_instruction (make_instruction pc OpSub)
                   (scan (ExpectOpcode (S pc)) tail)
      | 6%nat => prepend_instruction (make_instruction pc OpDup)
                   (scan (ExpectOpcode (S pc)) tail)
      | 7%nat => prepend_instruction (make_instruction pc OpJumpdest)
                   (scan (ExpectOpcode (S pc)) tail)
      | 8%nat => prepend_instruction (make_instruction pc OpJumpi)
                   (scan (ExpectOpcode (S pc)) tail)
      | raw => Rejected (UnknownOpcode pc raw)
      end
  | ExpectOperand pc LoadOperand, operand :: tail =>
      prepend_instruction
        (make_instruction pc (OpLoad (byte_nat operand)))
        (scan (ExpectOpcode (pc + 2)%nat) tail)
  | ExpectOperand pc StoreOperand, operand :: tail =>
      prepend_instruction
        (make_instruction pc (OpStore (byte_nat operand)))
        (scan (ExpectOpcode (pc + 2)%nat) tail)
  end.

Record program : Type := {
  program_bytes : list byte;
  program_code : list instruction
}.

Definition parse (bytes : list byte) : parse_result program :=
  match scan (ExpectOpcode 0) bytes with
  | Parsed code =>
      Parsed {| program_bytes := bytes; program_code := code |}
  | Rejected error => Rejected error
  end.

(** Program counters are offsets in the original byte string, not positions
    in [program_code].  Consequently the instruction after LOAD or STORE is
    two byte PCs later.  JUMPI accepts only a counter containing JUMPDEST. *)
Fixpoint instruction_at (pc : nat) (code : list instruction)
    : option instruction :=
  match code with
  | [] => None
  | i :: tail =>
      if Nat.eqb pc (instr_pc i) then Some i else instruction_at pc tail
  end.

Definition fetch (p : program) (pc : nat) : option instruction :=
  instruction_at pc (program_code p).

Definition opcode_is_jumpdest (op : opcode) : bool :=
  match op with
  | OpJumpdest => true
  | _ => false
  end.

Definition is_jumpdest (p : program) (pc : nat) : bool :=
  match fetch p pc with
  | Some i => opcode_is_jumpdest (instr_opcode i)
  | None => false
  end.

(** ** Machine state and execution *)

Definition word : Type := Z.
Definition word_modulus : Z := 2 ^ 256.
Definition normalize (w : word) : word := w mod word_modulus.

Definition word_is_zero (w : word) : bool := Z.eqb (normalize w) 0.
Definition word_to_pc (w : word) : nat := Z.to_nat (normalize w).

(** The head of [source_stack] is its top.  Input is immutable; STORE replaces
    one element of [source_outputs].  The lengths of both vectors remain
    constant during execution. *)
Record source_state : Type := {
  source_pc : nat;
  source_stack : list word;       (** The head is the top of the stack. *)
  source_inputs : list word;
  source_outputs : list word
}.

Inductive halt_reason : Type :=
  | HaltStop
  | HaltFallthrough
  | HaltStackUnderflow
  | HaltStackOverflow
  | HaltInvalidJump
  | HaltInputOutOfBounds
  | HaltOutputOutOfBounds.

Inductive configuration : Type :=
  | Running (state : source_state)
  | Halted (reason : halt_reason) (state : source_state).

Definition with_pc (st : source_state) (pc : nat) : source_state :=
  {| source_pc := pc;
     source_stack := source_stack st;
     source_inputs := source_inputs st;
     source_outputs := source_outputs st |}.

Definition with_stack (st : source_state) (stack : list word) : source_state :=
  {| source_pc := source_pc st;
     source_stack := stack;
     source_inputs := source_inputs st;
     source_outputs := source_outputs st |}.

Definition with_stack_pc
    (st : source_state) (stack : list word) (pc : nat) : source_state :=
  {| source_pc := pc;
     source_stack := stack;
     source_inputs := source_inputs st;
     source_outputs := source_outputs st |}.

Definition with_stack_outputs_pc
    (st : source_state) (stack outputs : list word) (pc : nat)
    : source_state :=
  {| source_pc := pc;
     source_stack := stack;
     source_inputs := source_inputs st;
     source_outputs := outputs |}.

Fixpoint replace_nth {A : Type}
    (index : nat) (value : A) (values : list A) : option (list A) :=
  match index, values with
  | O, _ :: tail => Some (value :: tail)
  | S index', head :: tail =>
      match replace_nth index' value tail with
      | Some tail' => Some (head :: tail')
      | None => None
      end
  | _, [] => None
  end.

(** The operand stack is limited to 1024 words. *)
Definition stack_limit (_ : program) : nat := 1024.

Definition push
    (p : program) (next : nat) (value : word) (st : source_state)
    : configuration :=
  if Nat.ltb (length (source_stack st)) (stack_limit p) then
    Running (with_stack_pc st (normalize value :: source_stack st) next)
  else
    Halted HaltStackOverflow st.

(** [source_step] executes exactly one instruction from a running state.

    - LOAD pushes the indexed input word.  An invalid index halts without
      changing the state.
    - STORE first checks the output index, then pops one value and writes it.
      An invalid index therefore takes precedence over stack underflow and
      leaves both stack and output unchanged.
    - ADD and SUB pop [rhs] first and [lhs] second, then push respectively
      [lhs + rhs] and [lhs - rhs], normalized modulo [2^256].
    - JUMPI pops [destination] first and [condition] second.  A zero condition
      falls through without validating [destination].  A nonzero condition
      transfers only to a parsed JUMPDEST; an invalid target halts after the
      two operands have been popped.

    STOP, faults, and fetching outside the parsed code halt.  There is no
    transition out of a [Halted] configuration. *)
Definition source_step (p : program) (st : source_state) : configuration :=
  match fetch p (source_pc st) with
  | None => Halted HaltFallthrough st
  | Some i =>
      match instr_opcode i with
      | OpStop => Halted HaltStop st
      | OpLoad index =>
          match nth_error (source_inputs st) index with
          | Some value => push p (instr_next i) value st
          | None => Halted HaltInputOutOfBounds st
          end
      | OpStore index =>
          if Nat.ltb index (length (source_outputs st)) then
            match source_stack st with
            | [] => Halted HaltStackUnderflow st
            | value :: rest =>
                match replace_nth index (normalize value) (source_outputs st) with
                | Some outputs =>
                    Running
                      (with_stack_outputs_pc st rest outputs (instr_next i))
                | None => Halted HaltOutputOutOfBounds st
                end
            end
          else
            Halted HaltOutputOutOfBounds st
      | OpPop =>
          match source_stack st with
          | [] => Halted HaltStackUnderflow st
          | _ :: rest => Running (with_stack_pc st rest (instr_next i))
          end
      | OpAdd =>
          match source_stack st with
          | rhs :: lhs :: rest =>
              push p (instr_next i) (lhs + rhs) (with_stack st rest)
          | _ => Halted HaltStackUnderflow st
          end
      | OpSub =>
          match source_stack st with
          | rhs :: lhs :: rest =>
              push p (instr_next i) (lhs - rhs) (with_stack st rest)
          | _ => Halted HaltStackUnderflow st
          end
      | OpDup =>
          match source_stack st with
          | [] => Halted HaltStackUnderflow st
          | value :: _ => push p (instr_next i) value st
          end
      | OpJumpdest => Running (with_pc st (instr_next i))
      | OpJumpi =>
          match source_stack st with
          | destination :: condition :: rest =>
              let popped := with_stack st rest in
              if word_is_zero condition then
                Running (with_pc popped (instr_next i))
              else
                let destination_pc := word_to_pc destination in
                if is_jumpdest p destination_pc then
                  Running (with_pc popped destination_pc)
                else
                  Halted HaltInvalidJump popped
          | _ => Halted HaltStackUnderflow st
          end
      end
  end.

Inductive source_small_step (p : program)
    : configuration -> configuration -> Prop :=
  | SourceStep : forall st next,
      source_step p st = next ->
      source_small_step p (Running st) next.

(** [run fuel p current] executes at most [fuel] source instructions.  Running
    out of fuel returns the current configuration, which may still be
    [Running]; a [Halted] configuration remains unchanged. *)
Fixpoint run (fuel : nat) (p : program) (current : configuration)
    : configuration :=
  match fuel with
  | O => current
  | S fuel' =>
      match current with
      | Running st => run fuel' p (source_step p st)
      | Halted _ _ => current
      end
  end.
