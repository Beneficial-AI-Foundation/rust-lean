#!/usr/bin/env bash
set -euxo pipefail

CRATE_DIR="rust/merkle_root_rs"
OUT_DIR="lean/MerkleRootLean/Extracted"

rm -rf "${OUT_DIR}"
mkdir -p "${OUT_DIR}"

pushd "${CRATE_DIR}"
  cargo hax into lean
  rsync -a --delete proofs/lean/extraction/ "../../${OUT_DIR}/"
popd

# Mark extracted definitions as noncomputable (they rely on uninterpreted Core.* stubs)
perl -pi -e 's/^def (Merkle_root_rs\.merkle_root_from_path)/noncomputable def $1/' lean/MerkleRootLean/Extracted/Merkle_root_rs.lean
perl -pi -e 's/^def (Merkle_root_rs\.merkle_verify_from_path)/noncomputable def $1/' lean/MerkleRootLean/Extracted/Merkle_root_rs.lean
