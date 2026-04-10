Plonky3's Field Arithmetic Extraction With Aeneas
----------------------------------------

✨ WIP ✨

This repository contains the Lean 4 verification efforts using [Aeneas](https://github.com/AeneasVerif/aeneas) of some field arithmetic crates from Plonky3.

Currently we are testing the capabilities of Aeneas to extract a Rust model of the Mersenne31 crate, with the aim of
verifying it against [CompPoly](https://github.com/Verified-zkEVM/CompPoly/).

## Repository Structure

- [`src/`](./src/) contains the Mersenne31 model that we are incrementally building.
- [`lean/`](./lean/) holds the extracted code and verification efforts.
- [`extract-aeneas.sh`](./extract-aeneas.sh) is the extraction script, which also modifies the extracted code for correctness.

## Extraction Targets

We're currently targeting [`fields.rs`](https://github.com/Plonky3/Plonky3/blob/main/field/src/field.rs)
and [`mersenne31.rs`](https://github.com/Plonky3/Plonky3/blob/main/mersenne-31/src/mersenne_31.rs),
with the corresponding incremental models in [`src/`](./src/).

## Further Documentation

Documentation for this repository can be devided into the following categories and found in the following places:
- Incremental construction of the Mersenne31 models and description on the encountered challenges: [`src/`](./src/) directory.
- Fixes to the extracted Lean code: commented in the [`extract-aeneas.sh`](./extract-aeneas.sh) file.
