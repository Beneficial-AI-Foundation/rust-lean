# Verification of one step FRI folding

## Project Structure

```
p3-hax-lean-fri-pipeline/
├── rust/p3_fri_kernel/
│   ├── src/lib.rs                           # Rust implementation
│   └── proofs/lean/extraction/
│       ├── p3_fri_kernel.lean               # Extracted code (compiles)
│       └── BasicProofs.lean                 # Basic properties (@TODO: prove!)
│
└── lean/P3FriProofs/                        # ArkLib integration
    ├── lakefile.toml                        # Updated to Lean 4.26.0
    ├── lean-toolchain                       # v4.26.0
    ├── P3FriProofs.lean                     # Main file with ArkLib imports
    └── Proofs/
        └── FoldingCorrectness.lean          # ArkLib verification (@TODO: prove!)
```

## Plonky3 function for verification

We take small, “pure” fragment FRI folding (one step/round) from Plonky3.

https://github.com/Plonky3/Plonky3/blob/main/fri/src/config.rs#L82

function `compute_log_arity_for_round` from `fri/src/config.rs`

## Hax -> Lean Extraction

We don't need a **patch file** in this example, 
but  we had to build hax from PR #1880 (upgrade to Lean 4.26.0)

## Basic Proof Infrastructure  

- file: `rust/p3_fri_kernel/proofs/lean/extraction/BasicProofs.lean` with 6 theorems and 3 examples (builds successfully)

## Aligned All Dependencies to Lean 4.26.0

- **ArkLib**: main branch (Lean 4.26.0)
- **CompPoly**: master branch (Lean 4.26.0)
- **Hax**: PR #1880 (Lean 4.26.0)

## Integrated ArkLib FRI Specifications

`lean/P3FriProofs/P3FriProofs.lean`

- imported FRI single round specs, polynomial folding, domain theory
- Connected our code to formal FRI specifications

ArkLib Integration
```
lean/P3FriProofs/
├── P3FriProofs.lean                 # Main file with ArkLib imports
├── Proofs/FoldingCorrectness.lean   # Here we will have folding correctness proofs
├── lakefile.toml                    # All deps at Lean 4.26.0
└── lean-toolchain                   # v4.26.0
```

there are some name conflicts discovered between ArkLib and Hax (for example both define ToNat). 
to solve such conflicts we should import specific modulees of ArkLib (instead of import ArkLib)

### FRI Specifications from ArkLib

- **Single Round**: `ArkLib/ProofSystem/Fri/Spec/SingleRound.lean`
  - Folding degree parameters (`s`)
  - Domain size constraints
  - Statement and witness types

- **Polynomial Operations**: `ArkLib/Data/Polynomial/SplitFold.lean`
  - `splitNth` - n-way polynomial splitting
  - `foldNth` - polynomial folding with powers of α

- **Round Consistency**: `ArkLib/ProofSystem/Fri/RoundConsistency.lean`
  - Properties between consecutive rounds