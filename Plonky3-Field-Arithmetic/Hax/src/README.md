Mersenne31 Incremental Models
-----------------------------

The aim of this repository is to extract and verify Plonky3's
[`mersenne31.rs`](https://github.com/Plonky3/Plonky3/blob/main/mersenne-31/src/mersenne_31.rs)
against [Arklib](https://github.com/Verified-zkEVM/ArkLib).
To this end we are incrementally building models of the original code to identify how to best adapt the targeted Rust for
Lean 4 extraction via [Hax](https://hax.cryspen.com/).

## File Description

All files in this directory are Hax-friendly partial versions of their Plonky3 counterparts.

- [`field.rs`](./field.rs): Models [`field.rs`](https://github.com/Plonky3/Plonky3/blob/main/field/src/field.rs).
This file contains the associated field trait definitions of which the Mersenne31 field is an implementation of.
- [`mersenne31.rs`](./mersenne31): Models [`mersenne31.rs`](https://github.com/Plonky3/Plonky3/blob/main/mersenne-31/src/mersenne_31.rs).
Contains the logic of the Mersenne31 field and associated trait implementations.

## Hax Adaptations

The following is a description of Rust changes we had to make to the targeted code to obtain better Lean 4 generated code.
For a more detailed diff between the original Rust and our models we recommend looking at the annotations in our models.

### Mutual Trait Dependency

There is a decent amount of mutual dependency in the traits of `field.rs`. While this is not problematic in Rust, mutually dependent
definitions are [not supported in Hax](https://github.com/cryspen/hax/issues/1886#issuecomment-3784811917) yet.

As an example of how this mutual dependency shows in `field.rs`, consider the definition of trait `PrimeCharacteristicRing`:

```rust
pub trait PrimeCharacteristicRing:
    Sized
    + ...
{
    /// The field `ℤ/p` where the characteristic of this ring is p.
    type PrimeSubfield: PrimeField;

    const ZERO: Self;
    const ONE: Self;
    // etc.
```
The associated type of `PrimeCharacteristicRing` is of type `PrimeField`, which is defined as...
```rust
pub trait PrimeField:
    Field
    + ...
```
And then the `Field` trait has `Algebra<Self>` as a supertrait, which in turn has `PrimeCharacteristicRing` as a superfield.

See [this issue](https://github.com/cryspen/hax/issues/1773) for more context on the Hax side.

### Equality Constraints and Trait Bounds on Associated Types

Let's look again at the `PrimeCharacteristicRing` definition:

```rust
pub trait PrimeCharacteristicRing:
    Sized
    + Default
    + Clone
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Neg<Output = Self>
    + Mul<Output = Self>
    + MulAssign
    + Sum
    + Product
    + Debug
{
    /// The field `ℤ/p` where the characteristic of this ring is p.
    type PrimeSubfield: PrimeField;

    const ZERO: Self;
    // etc.
```
Here we can see two features of associated types that are [not yet supported](https://github.com/cryspen/hax/issues/1710) by Hax:
equality constraints (e.g., `Add<Output = Self>`) and trait bounds (e.g., `type PrimeSubfield: PrimeField;`).

For both cases we have commented out the annotations.
We will be following [the approach](https://github.com/cryspen/hax/issues/1886#issuecomment-3785220213)
of relaxing these restrictions at the trait level while making sure that the logic at the implementation
level remains equivalent to the original implementation if not the same.

### Unimplemented Traits and Functions

Some traits traits are not implemented on the Hax side are needed in order to perform a full extraction. So far, we have missed the
implementation of the [`Iterator`](https://doc.rust-lang.org/src/core/iter/traits/iterator.rs.html) trait, since both the
[`Sum` and `Product`](https://doc.rust-lang.org/src/core/iter/traits/accum.rs.html) supertraits of the `PrimeCharacteristicRing`
trait depend on it.

Another case of unimplemented code are functions lacking implementations on the Hax side (e.g., `overflowing_add`).
However, for these cases we provide an implementation in [`HaxPatch.lean`](../lean/Mersenne31/HaxPatch.lean)
in order to not modify the Rust code.
