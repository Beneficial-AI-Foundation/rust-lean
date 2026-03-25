import Lake
open Lake DSL

package FoldStepVerif where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends/lean"

require ArkLib from git
  "https://github.com/Verified-zkEVM/ArkLib" @ "main"

-- Aeneas-extracted code
lean_lib FoldStep

-- Core verification (Aeneas only, no ArkLib)
@[default_target]
lean_lib FoldStepVerif

-- ArkLib-based proofs (separate target due to BitVec.toNat_pow collision)
-- Build with: `lake build FoldStepVerifArkLib`
@[default_target]
lean_lib FoldStepVerifArkLib where
  roots := #[`FoldStepVerif.FoldingCorrectness]
