# Verified zkEVM

A collection of formal verification projects for zero-knowledge virtual machine components. Each subdirectory is a self-contained project where Rust code is translated to Lean 4 using [Hax](https://github.com/cryspen/hax) or [Aeneas](https://github.com/AeneasVerif/aeneas), and then formally verified.

## Projects

| Directory | Pipeline | Description |
|-----------|----------|-------------|
| `hax-FRI/` | Hax → Lean | Verification of one-step FRI folding from [Plonky3](https://github.com/Plonky3/Plonky3) |
| `hax-horner/` | Hax → Lean | Horner polynomial evaluation from Plonky3, with CompPoly spec and proofs |
| `hax-merkle/` | Hax → Lean | Merkle root recomputation and inclusion verification from [RISC Zero](https://github.com/risc0/risc0) |
| `hax-annotations-adc/` | Hax → Lean | 32-bit limb addition with carry (`adc`), verified via Hax annotations and `bv_decide` |
| `aeneas-FRI/` | Aeneas → Lean | FRI folding functions (`fold_step`, `fold_arity`) translated via the Aeneas pipeline |

Each project has its own README with details on the verification target, pipeline specifics, and current status.

## Building

Each Lean project can be built independently with `lake build` from its respective directory. Rust crates can be built with `cargo build`. See individual project READMEs for specific instructions.
