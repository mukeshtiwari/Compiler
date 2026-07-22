#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

if ! command -v coqdoc >/dev/null 2>&1; then
  echo "coqdoc was not found in PATH. Install Rocq/Coq documentation tools first." >&2
  exit 1
fi

echo "[1/3] Building Rocq theories"
dune build

echo "[2/3] Generating Coqdoc HTML"
mkdir -p doc/html

coqdoc --html --utf8 --toc \
  -R src/Bytecode Bytecode \
  -R src/Assembly Assembly \
  -R src/Proofs Proofs \
  -R src/Extraction Extraction \
  -R coq-compcert.3.17/lib compcert.lib \
  -R coq-compcert.3.17/common compcert.common \
  -R coq-compcert.3.17/x86 compcert.x86 \
  -R coq-compcert.3.17/x86_64 compcert.x86_64 \
  -R coq-compcert.3.17/backend compcert.backend \
  -R coq-compcert.3.17/cfrontend compcert.cfrontend \
  -R coq-compcert.3.17/driver compcert.driver \
  -R coq-compcert.3.17/cparser compcert.cparser \
  -R coq-compcert.3.17/flocq Flocq \
  -R coq-compcert.3.17/MenhirLib MenhirLib \
  -d doc/html \
  src/Bytecode/Bytecode.v \
  src/Assembly/Assembly.v \
  src/Proofs/Proof.v \
  src/Proofs/CorrectnessStatements.v \
  src/Extraction/ExtractCompiler.v

echo "[3/3] Done"
echo "Coqdoc index: doc/html/index.html"
