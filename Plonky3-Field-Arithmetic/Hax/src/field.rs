use core::ops::{Add, AddAssign, // Div, DivAssign,
                Mul, MulAssign, Neg, Sub, SubAssign};

// use core::iter::{Product, Sum}; // Missing from Hax
use crate::unimplemented::{Product, Sum};

/// NOTE: DUMMY PLACEHOLDER. Missing `PrimeField`
/// A prime field `ℤ/p` with order, `p < 2^64`.
pub trait PrimeField64 // : PrimeField
{
    const ORDER_U64: u64;

    fn as_canonical_u64(&self) -> u64;

    fn to_unique_u64(&self) -> u64 {
        // A simple default which is optimal for some fields.
        self.as_canonical_u64()
    }
}

/// NOTE: DUMMY PLACEHOLDER. Missing `PrimeField` and `PrimeField64`
/// NOTE: `PrimeField64` supertrait removed to avoid circularities in the implementation
/// A prime field `ℤ/p` with order `p < 2^32`.
pub trait PrimeField32 // : PrimeField64
{
    const ORDER_U32: u32;

    fn as_canonical_u32(&self) -> u32;

    fn to_unique_u32(&self) -> u32 {
        // A simple default which is optimal for some fields.
        self.as_canonical_u32()
    }
}

/// NOTE: Removed the equality constraint of associated type for supertraits
pub trait PrimeCharacteristicRing:
    Sized
    + Default
    + Clone
    + Add// <Output = Self>
    + AddAssign
    + Sub// <Output = Self>
    + SubAssign
    + Neg// <Output = Self>
    + Mul// <Output = Self>
    + MulAssign
    + Sum
    + Product
{
    /// NOTE: This associated type is unbounded. It is originally bounded to `PrimeField`.
    ///       Hax doesn't currently support associated types bounds nor mutually
    ///       dependent traits.
    type PrimeSubfield; // : PrimeField;

    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;
    const NEG_ONE: Self;

    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self;

    fn from_bool(b: bool) -> Self {
        // Some rings might reimplement this to avoid the branch.
        if b { Self::ONE } else { Self::ZERO }
    }

    /// Modified from the original to fit Hax's extraction constraints. Original:
    /// fn double(&self) -> Self {
    ///     self.clone() + self.clone()
    /// }
    fn double<A : Clone + Add>(a : &A) -> A::Output {
        a.clone() + a.clone()
    }

    /// NOTE: Dummy implementation
    fn halve(&self) -> Self {
        // This must be overwritten by PrimeField implementations as this definition
        // is circular when PrimeSubfield = Self. It should also be overwritten by
        // most rings to avoid the multiplication.
        // let half = Self::from_prime_subfield(Self::PrimeSubfield::ONE.halve());
        // self.clone() * half
        self.clone()
    }

}

