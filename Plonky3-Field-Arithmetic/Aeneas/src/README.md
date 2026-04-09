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
- [`mersenne31.rs`](./mersenne31.rs): Models [`mersenne31.rs`](https://github.com/Plonky3/Plonky3/blob/main/mersenne-31/src/mersenne_31.rs).
Contains the logic of the Mersenne31 field and associated trait implementations.

## Aeneas Adaptations

> Aeneas version: commit [`1180be60`](https://github.com/AeneasVerif/aeneas/commit/1180be60c7a0e642cb442bfe90fe5cd8c1bb853f)

The following is a description of Rust changes we made to the targeted code to obtain better Lean 4 generated code.
For a more detailed diff between the original Rust and our models we recommend looking at the comment annotations in our models.

1. [Mocked Standard Library Types](#1-mocked-standard-library-types)
2. [Removed Mutually Recursive Trait Bounds](#2-removed-mutually-recursive-trait-bounds)
3. [Restricted `QuotientMap` Instances](#3-restricted-quotientmap-instances)
4. [`debug_assert!` Replaced with `assert!`](#4-debug_assert-replaced-with-assert)
5. [Abstract Methods in `PrimeCharacteristicRing`](#5-abstract-methods-in-primecharacteristicring)
6. [Explicitly Copied `Ord` Methods](#6-explicitly-copied-ord-methods)
7. [Dropped `Sum`, `Product`, and `Debug` Supertraits](#7-dropped-sum-product-and-debug-supertraits)
8. [Unsupported Features Commented Out](#8-unsupported-features-commented-out)

### 1. Mocked Standard Library Types

**Applies to:** [`field.rs`](./field.rs), [`mersenne31.rs`](./mersenne31.rs), [`mocks.rs`](./mocks.rs)

`core::hash::{Hash, Hasher}` are replaced with local mock definitions in [`mocks.rs`](./mocks.rs). `Hash` and `Hasher` are mocked because Aeneas's built-in model for `Hasher` does not include `write_u32`, which is needed by `Mersenne31`'s [`Hash` implementation](https://github.com/AeneasVerif/aeneas/blob/28ad838ca560c469a1c8a2db4e89a87f9900a11b/backends/lean/Aeneas/Std/Core/Hash.lean#L6-L9).

### 2. Removed Mutually Recursive Trait Bounds

**Applies to:** [`field.rs`](./field.rs)
**Tracking issue:** https://github.com/AeneasVerif/aeneas/issues/176

The associated type `PrimeCharacteristicRing::PrimeSubfield` originally carries a `: PrimeField` bound, which creates a mutual recursion between `PrimeCharacteristicRing` and `PrimeField` (each depends on the other). Aeneas does not support mutually recursive trait declarations, so the bound is removed and the associated type is left unbounded.

### 3. Restricted `QuotientMap` Instances

**Applies to:** [`field.rs`](./field.rs), [`mersenne31.rs`](./mersenne31.rs)

`PrimeField` originally requires `QuotientMap` instances for many integer types (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i32`, `i64`, `i128`, `isize`). In our model this is restricted:

- **Implemented** (`mersenne31.rs`): `u32`, `i32`, `u64`, and `i64` only; all others are commented out.
- **Required as supertrait bounds** (`field.rs`): `u32`, `i32`, `u64`, and `i64`; all others are commented out.

### 4. `debug_assert!` Replaced with `assert!`

**Applies to:** [`mersenne31.rs`](./mersenne31.rs), [`util.rs`](./util.rs)

All uses of `debug_assert!` are replaced with `assert!`. Using `assert!` ensures the generated Lean code includes the corresponding precondition checks and proof obligations.

### 5. Abstract Methods in `PrimeCharacteristicRing`

**Applies to:** [`field.rs`](./field.rs), [`mersenne31.rs`](./mersenne31.rs), [`util.rs`](./util.rs)

Three methods in `PrimeCharacteristicRing` have their default bodies replaced or removed, each for related but distinct reasons:

- **`div_2exp_u64`**: the default body is commented out in `field.rs`. The original default references `halve()` and `exp_u64()` on `PrimeSubfield`, which is circular when `PrimeSubfield = Self` and impossible given the [removed `PrimeField` bound](#2-removed-mutually-recursive-trait-bounds). The method is left abstract and implemented concretely in `mersenne31.rs` as a right bit-rotation by `exp` positions.
- **`mul_2exp_u64`**: similarly as in the above bulletpoint, the default body references `exp_u64()` on `Self::TWO`, which [is circular](#2-removed-mutually-recursive-trait-bounds). Left abstract in `field.rs` and implemented concretely in `mersenne31.rs` as a left bit-rotation by `exp` positions.
- **`halve()`**: the default body is also circular (`PrimeSubfield::ONE.halve()` when `PrimeSubfield = Self`). Rather than being left fully abstract, the default in `field.rs` is kept as a stub returning `self.clone()`. `mersenne31.rs` overrides it concretely using `halve_u32::<P>`, a helper copied into `util.rs` that computes `x/2`.

### 6. Explicitly Copied `Ord` Methods

**Applies to:** [`mersenne31.rs`](./mersenne31.rs)

- `Ord::max`, `Ord::min`, and `Ord::clamp` are explicitly overridden in `impl Ord for Mersenne31` with inline definitions. Aeneas does not extract these methods from the default trait implementations, so they must be present directly in the `impl` block to appear in the generated Lean code.
- `clamp` includes a redundant `assert!(max >= min)` alongside the standard `assert!(min <= max)`. The extra assertion is needed for Aeneas to emit a `ge` predicate in the generated Lean code.

### 7. Dropped `Sum`, `Product`, and `Debug` Supertraits

**Applies to:** [`field.rs`](./field.rs), [`mersenne31.rs`](./mersenne31.rs)

`Sum`, `Product`, and `Debug` are removed as supertraits of `PrimeCharacteristicRing` in `field.rs`, and the `Sum` and `Product` `impl` blocks for `Mersenne31` in `mersenne31.rs` are removed entirely. Proper iterator handling is not yet fully supported by the extraction pipeline, and these traits are not needed for the arithmetic operations currently being verified.

### 8. Unsupported Features Commented Out

**Applies to:** [`field.rs`](./field.rs), [`mersenne31.rs`](./mersenne31.rs)

Several features from the original code are not yet modelled:

- `Mersenne31::new_array` (`mersenne31.rs`): constructs a field element array using a `const` `while` loop. Commented out to make it an explicit future work item.
- `Field::add_slices` (`field.rs`): operates over mutable slices and packed field elements. Commented out to make it an explicit future work item.
- Various trait bounds on `Field` in `field.rs` (`RawDataSerializable`, `Packable`, `Display`, `Serialize`, `DeserializeOwned`) are removed as they are not relevant to the arithmetic being verified.
