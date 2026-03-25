#!/usr/bin/env bash
set -euxo pipefail

CRATE_DIR="rust/horner_eval_rs"
OUT_DIR="lean-compoly/CompPolyEval/Extracted"

rm -rf "${OUT_DIR}"
mkdir -p "${OUT_DIR}"

pushd "${CRATE_DIR}"
  cargo hax into lean
  rsync -a --delete proofs/lean/extraction/ "../../${OUT_DIR}/"
popd

