Plonky3's Mersenne31 Extraction With Hax
----------------------------------------

✨ WIP ✨

This repository contains the Lean 4 verification efforts using Hax of the Mersenne31 crate from Plonky3.

Currently we are testing the capabilities of Hax to extract the actual code from the Mersenne31 crate, with the aim of
verifying it against [Arklib](https://github.com/Verified-zkEVM/ArkLib).

## Repository Structure

- [`src/`](./src/) contains the Mersenne31 models that we are incrementally building.
- [`lean/`](./lean/) holds the extracted code and verification efforts.
- [`extract.sh`](./extract.sh) is the extraction script, which also modifies the extracted code for correctness.

## Extraction Targets

We're currently targeting [`fields.rs`](https://github.com/Plonky3/Plonky3/blob/main/field/src/field.rs)
and [`mersenne31.rs`](https://github.com/Plonky3/Plonky3/blob/main/mersenne-31/src/mersenne_31.rs),
with the corresponding incremental models in [`src/`](./src/).

## Further Documentation

Documentation for this repository can be devided into the following categories and found in the following places:
- Incremental construction of the Mersenne31 models and description on the encountered challenges: [`src/`](./src/) directory.
- Fixes to the extracted Lean code: commented in the [`extract.sh`](./extract.sh) file.
- Missing Hax implementations needed for the edited extracted Lean to work: [`HaxPatch.lean`](./lean/Mersenne31/HaxPatch.lean)
