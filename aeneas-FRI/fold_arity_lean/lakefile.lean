import Lake
open Lake DSL

package FoldArityVerif where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends/lean"

require ArkLib from git
  "https://github.com/Verified-zkEVM/ArkLib" @ "main"

-- so the Aeneas-extracted code can be imported as dependency
lean_lib FoldArity

@[default_target]
lean_lib FoldArityVerif

-- Separate target: FoldingCorrectness imports ArkLib (Batteries/mathlib),
-- which conflicts with Aeneas on `BitVec.toNat_pow`.
-- Built independently: `lake build FoldArityVerifArkLib`
@[default_target]
lean_lib FoldArityVerifArkLib where
  roots := #[`FoldArityVerif.FoldingCorrectness]
