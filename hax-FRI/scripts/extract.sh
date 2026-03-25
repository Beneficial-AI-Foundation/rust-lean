#!/usr/bin/env bash
set -euo pipefail

cd rust/p3_fri_kernel

# примерная форма; уточним после выбора кода
cargo hax -C proofs/lean/extraction

