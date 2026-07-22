#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

BYTECODE_FILE="${1:-tools/tmp/add_store.bc}"
BIN_PATH="${2:-tools/bin/run_bytecode_x86}"
INPUT_BIN="${3:-tools/tmp/in_words.bin}"
OUTPUT_BIN="${4:-tools/tmp/out_words.bin}"

mkdir -p tools/tmp tools/bin

if ! command -v xxd >/dev/null 2>&1; then
  echo "xxd is required for demo generation and inspection." >&2
  exit 1
fi

# Bytecode program:
# LOAD 0; LOAD 1; ADD; STORE 0; STOP
printf '\x01\x00\x01\x01\x04\x02\x00\x00' > "$BYTECODE_FILE"

word_hex() {
  printf '%064x' "$1"
}

# Two 256-bit words in big-endian byte order: [41, 1]
{
  word_hex 41
  word_hex 1
} | xxd -r -p > "$INPUT_BIN"

./tools/build_and_link_wrapper.sh "$BYTECODE_FILE" "$BIN_PATH"
"$BIN_PATH" "$INPUT_BIN" "$OUTPUT_BIN"

FIRST_WORD_HEX="$(xxd -p -l 32 "$OUTPUT_BIN" | tr -d '\n')"
EXPECTED_HEX="$(word_hex 42)"

echo "First output word (hex): $FIRST_WORD_HEX"
echo "Expected first word  (hex): $EXPECTED_HEX"

if [[ "$FIRST_WORD_HEX" == "$EXPECTED_HEX" ]]; then
  echo "Demo check passed: out[0] = 42"
else
  echo "Demo check failed: out[0] is not 42" >&2
  exit 1
fi
