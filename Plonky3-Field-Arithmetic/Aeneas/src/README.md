Mersenne31 Incremental Models
-----------------------------

The aim of this repository is to extract and verify Plonky3's
[`mersenne31.rs`](https://github.com/Plonky3/Plonky3/blob/main/mersenne-31/src/mersenne_31.rs)
against [CompPoly](https://github.com/Verified-zkEVM/CompPoly/).
To this end we are incrementally building models of the original code to identify how to best adapt the targeted Rust for
Lean 4 extraction via [Aeneas](https://github.com/AeneasVerif/aeneas).

## File Description

All files in this directory are Hax-friendly partial versions of their Plonky3 counterparts.

- [`field.rs`](./field.rs): Models [`field.rs`](https://github.com/Plonky3/Plonky3/blob/main/field/src/field.rs).
This file contains the associated field trait definitions of which the Mersenne31 field is an implementation of.
- [`mersenne31.rs`](./mersenne31): Models [`mersenne31.rs`](https://github.com/Plonky3/Plonky3/blob/main/mersenne-31/src/mersenne_31.rs).
Contains the logic of the Mersenne31 field and associated trait implementations.

## Aeneas Adaptations

The following is a description of Rust changes we had to make to the targeted code to obtain better Lean 4 generated code.
For a more detailed diff between the original Rust and our models we recommend looking at the annotations in our models.

TBD.
