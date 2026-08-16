```markdown
# Take-Home Exercise: Verified Bytecode Compiler

**You are expected to use LLMs or coding agents;** a manual solution would take substantially longer. Please include complete transcripts. What matters is that you understand your submission — we'll walk through your compiler, your correctness statements, and your tradeoffs in a follow‑up conversation.

---

## The Task

Your task is to implement a compiler from the bytecode below to **x86‑64 assembly** and mechanically prove it correct in **Rocq**. The compiler may be written in Gallina, Rocq's built‑in functional language.

The compiler translates a byte string into a native function operating on two flat arrays of 32‑byte words: `in` is read‑only and `out` is mutable. Words in both arrays use **big‑endian** byte order. The function has this signature:

```c
using uint = unsigned int;
extern void f(unsigned char* in, uint insize, unsigned char* out, uint outsize);
```

- `insize` and `outsize` are numbers of **32‑byte words**, not byte counts.
- Assume `uint` is exactly **32 bits**.

The supplied Rocq file defines the byte type, parser, source state, fault behavior, one‑step semantics, and fuel‑bounded evaluator. It is the authoritative source‑language specification. The attachment is plain text; if your browser retains Notion's final `.txt` suffix, rename it to `Bytecode.v`:

> **Bytecode.v** (13.5 KiB) – provided separately.

To state and prove correctness, you will need a **formal x86 semantics**. You may use any existing formalization, such as CompCert or Jasmin.

---

## Instruction Set

| Opcode | Operands | Behaviour |
|--------|----------|-----------|
| `0x00 STOP` | none | Halts execution. |
| `0x01 LOAD` | 1 byte: index into `in` | If `i < insize`, push `in[i]`; otherwise halt without changing the stack. |
| `0x02 STORE` | 1 byte: index into `out` | First check `i < outsize`. If false, halt without changing the stack. If true, pop the top word and write it to `out[i]`. |
| `0x03 POP` | none | Discard the top word. |
| `0x04 ADD` | none | Pop `rhs`, then `lhs`; push `lhs + rhs` modulo \(2^{256}\). |
| `0x05 SUB` | none | Pop `rhs`, then `lhs`; push `lhs - rhs` modulo \(2^{256}\). |
| `0x06 DUP` | none | Push a copy of the top word. |
| `0x07 JUMPDEST` | none | Mark this byte offset as a valid jump target; a no‑op at runtime. |
| `0x08 JUMPI` | none | Pop `destination`, then `condition`. If the condition is nonzero, jump to the destination. Both words are consumed whether or not the jump is taken. |

- Program counters and jump destinations are **byte offsets**.
- A taken `JUMPI` destination must be the byte offset of a **parsed `JUMPDEST`**; backward jumps are allowed.
- A zero condition falls through without validating the destination.

The operand stack contains **at most 1024 words**. Arithmetic is modulo \(2^{256}\). Stack underflow, stack overflow, invalid jumps, out‑of‑bounds I/O, `STOP`, and falling off the parsed program all halt the generated function. The void interface does not return a halt reason. Refer to `Bytecode.v` for exact corner‑case behavior.

---

## Theorem Statements

The most important design task is to **formulate the correctness statements**. We will mainly evaluate your compiler and the statements of the correctness theorems you prove about it. We likely will not have time to read the Rocq proof scripts in detail.

Therefore, the compiler implementation and correctness statements must be **understandable without reading the proof files**. Document the compiler with Coqdoc, and keep both the compiler interface and correctness statements as simple and concise as possible.

Place the correctness statements in a **designated file**. This file must **not** contain their Rocq proofs. Instead, include a concise English explanation of the overall proof, ideally written **without using AI**. The explanation may refer to Rocq lemmas or definitions in the proof files; a separate proof sketch for every statement is not required.

You may include useful correctness statements that you could not prove within the time limit. Clearly distinguish these from statements that have been proved.

---

## Wrapper

The following caller illustrates the native interface. Your generated output should be linkable against it.

```cpp
#include <cassert>
#include <cstring>
#include <fstream>
#include <ios>
#include <limits>
#include <memory>

using uint = unsigned int;
static_assert(sizeof(uint) == 4);

extern void f(unsigned char* in, uint insize, unsigned char* out, uint outsize);

int main(int const argc, char const* argv[]) {
    assert(argc == 3);

    uint const outsize = 10;
    std::size_t const out_bytes = 32 * static_cast<std::size_t>(outsize);
    std::unique_ptr<unsigned char[]> in;
    std::unique_ptr<unsigned char[]> out;
    uint insize = 0;

    {
        std::ifstream in_file(argv[1], std::ios::binary | std::ios::ate);
        auto const end = in_file.tellg();
        assert(end >= 0);
        std::size_t const in_bytes = static_cast<std::size_t>(end);
        assert(in_bytes % 32 == 0);
        assert(in_bytes / 32 <= std::numeric_limits<uint>::max());
        insize = static_cast<uint>(in_bytes / 32);
        in_file.seekg(0, std::ios::beg);
        in.reset(new unsigned char[in_bytes]);
        in_file.read(reinterpret_cast<char*>(in.get()), in_bytes);
        assert(in_file.gcount() == static_cast<std::streamsize>(in_bytes));
    }

    out.reset(new unsigned char[out_bytes]);
    std::memset(out.get(), 0, out_bytes);

    f(in.get(), insize, out.get(), outsize);

    {
        std::ofstream out_file(argv[2], std::ios::binary);
        out_file.write(reinterpret_cast<char const*>(out.get()), out_bytes);
    }

    return 0;
}
```

---


```
