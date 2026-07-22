#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

mkdir -p _build/default/tools/generated tools/generated tools/bin

echo "[1/3] Building extraction target"
dune build src/Extraction/ExtractCompiler.vo

echo "[2/3] Copying extracted compiler"
cp _build/default/tools/generated/compiler_extracted.ml tools/generated/compiler_extracted.ml

echo "[3/3] Building emitter binary"
ocamlc -c -o tools/generated/compiler_extracted.cmo tools/generated/compiler_extracted.ml
ocamlc -I tools/generated -c -o tools/bin/emit_f.cmo tools/emit_f.ml
ocamlc -o tools/bin/emit_f tools/generated/compiler_extracted.cmo tools/bin/emit_f.cmo

echo "Emitter ready at tools/bin/emit_f"
