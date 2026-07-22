#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

if [[ $# -lt 1 || $# -gt 4 ]]; then
  echo "Usage: $0 <bytecode.bc> [binary_path] [input_words.bin output_words.bin]"
  echo "Example build only: $0 tools/tmp/add_store.bc"
  echo "Example build+run:  $0 tools/tmp/add_store.bc tools/bin/run_bytecode_x86 tools/tmp/in.bin tools/tmp/out.bin"
  exit 2
fi

BYTECODE_FILE="$1"
BINARY_PATH="${2:-tools/bin/run_bytecode_x86}"
INPUT_BIN="${3:-}"
OUTPUT_BIN="${4:-}"

if [[ ! -f "$BYTECODE_FILE" ]]; then
  echo "Bytecode file not found: $BYTECODE_FILE" >&2
  exit 1
fi

ARCH_FLAGS=()
if [[ "$(uname -s)" == "Darwin" ]]; then
  ARCH_FLAGS=("-arch" "x86_64")
fi

mkdir -p tools/tmp tools/bin

./tools/build_emitter.sh
./tools/bin/emit_f "$BYTECODE_FILE" tools/tmp/f.s f
clang "${ARCH_FLAGS[@]}" -c tools/tmp/f.s -o tools/tmp/f.o
clang++ "${ARCH_FLAGS[@]}" -std=c++17 tools/wrapper_main.cpp tools/tmp/f.o -o "$BINARY_PATH"

echo "Built wrapper binary: $BINARY_PATH"

echo "Checking exported symbol in f.o"
if [[ "$(uname -s)" == "Darwin" ]]; then
  nm -gU tools/tmp/f.o | grep ' _f$' || true
else
  nm -g tools/tmp/f.o | grep ' f$' || true
fi

if [[ -n "$INPUT_BIN" || -n "$OUTPUT_BIN" ]]; then
  if [[ -z "$INPUT_BIN" || -z "$OUTPUT_BIN" ]]; then
    echo "Provide both input and output paths to run the binary." >&2
    exit 2
  fi
  "$BINARY_PATH" "$INPUT_BIN" "$OUTPUT_BIN"
  echo "Wrote output file: $OUTPUT_BIN"
fi
