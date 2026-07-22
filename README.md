# Verified Bytecode Compiler (Rocq + x86-64)

## Time Spent 
1. Actual human time spent 7 hours (Agents took more time).

## Reading order

1. `src/Bytecode/Bytecode.v`
	- Source language: bytecode syntax, parser, and small-step evaluator.
2. `src/Assembly/Assembly.v`
	- Compiler from parsed bytecode program to CompCert x86-64 Asm function.
3. `src/Proofs/Proof.v`
	- Main correctness theorem and proof skeleton (parametric target semantics). The proof relies on a number of axioms that, ideally, should be proved. However, doing so would require considerable time and a deep understanding of CompCert's x86 memory model.
4. `src/Proofs/CorrectnessStatements.v`
	- Statement-only specification of the generic compiler-correctness theorem, separated from the proof terms.
5. `src/Extraction/ExtractCompiler.v`
	- Extraction entrypoint for emitting a concrete assembly artifact.
6. `tools/emit_f.ml`
	- OCaml emitter that consumes extracted compiler output and writes x86-64 assembly.

## High-level Correctness Idea (Lockstep simulation)

If a bytecode program p_bytecode and its compiled x86 counterpart p_x86 are executed from equivalent initial states, then their output vectors remain identical at every step of the execution (since input vectors are immutable, there is no need to compare them at each step).

```OCaml
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
```


## What this adds for wrapper linkage

The project now includes a concrete artifact pipeline that generates an exported native symbol `f`:

- Input: raw bytecode file (`.bc`)
- Output assembly: `f.s`
- Output object: `f.o` exporting symbol `f` (mangled as `_f` on macOS)

This makes the generated function directly linkable with the provided C++ wrapper.

## Build Rocq theories
1. From the source directory, run `cd coq-compcert.3.17/` and once you are inside the Compcert, run `./make`.
2. Now run `dune build` from the source directory. 

## Generate Coqdoc HTML (one command)

```bash
make doc
```

This generates documentation for the main project files into `doc/html/`.

## Generate CompCert Coqdoc HTML

```bash
make doc-compcert
```

This delegates to CompCert's existing documentation target and writes under
`coq-compcert.3.17/doc/html/`.

## Build the emitter tool

```bash
./tools/build_emitter.sh
```

This does:

1. Builds `src/Extraction/ExtractCompiler.vo` (which writes extracted OCaml under `_build/default/tools/generated/`).
2. Copies extraction output to `tools/generated/compiler_extracted.ml`.
3. Builds `tools/bin/emit_f`.

## Generate x86-64 assembly symbol `f`

```bash
./tools/bin/emit_f <input.bc> <output.s> f
```

Example:

```bash
printf '\x01\x00\x01\x01\x04\x02\x00\x00' > tools/tmp/add_store.bc
./tools/bin/emit_f tools/tmp/add_store.bc tools/tmp/f.s f
```

## Assemble to object file

On Apple Silicon/macOS, force x86-64 target:

```bash
clang -arch x86_64 -c tools/tmp/f.s -o tools/tmp/f.o
```

On x86-64 Linux:

```bash
clang -c tools/tmp/f.s -o tools/tmp/f.o
```

## Verify exported symbol

```bash
nm -gU tools/tmp/f.o | grep ' _f$'   # macOS
```

Expected output includes:

```text
0000000000000000 T _f
```

## Linking note for C++ wrapper

Use C linkage in the wrapper declaration to avoid C++ name mangling:

```cpp
extern "C" void f(unsigned char* in, unsigned int insize,
						unsigned char* out, unsigned int outsize);
```

## One-command build and link with wrapper

Build `f.o` from bytecode and link it with the C++ wrapper in one command:

```bash
./tools/build_and_link_wrapper.sh <bytecode.bc>
```

Example:

```bash
./tools/build_and_link_wrapper.sh tools/tmp/add_store.bc
```

This produces a runnable binary at `tools/bin/run_bytecode_x86` by default.

To build and run immediately:

```bash
./tools/build_and_link_wrapper.sh <bytecode.bc> <binary_path> <input_words.bin> <output_words.bin>
```

## One-command end-to-end demo

Run a full demo that:

1. Generates example bytecode (`LOAD 0; LOAD 1; ADD; STORE 0; STOP`).
2. Generates big-endian input words `[41, 1]`.
3. Builds emitter and wrapper binary.
4. Runs the binary.
5. Checks that the first output word is `42`.

```bash
./tools/run_demo_add_store.sh
```