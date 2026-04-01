use crate::mocks::Hash;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use num_bigint::BigUint;

/// A prime field `ℤ/p` with order, `p < 2^64`.
pub trait PrimeField64: PrimeField {
    const ORDER_U64: u64;

    fn as_canonical_u64(&self) -> u64;

    fn to_unique_u64(&self) -> u64 {
        // A simple default which is optimal for some fields.
        self.as_canonical_u64()
    }
}

/// A prime field `ℤ/p` with order `p < 2^32`.
pub trait PrimeField32: PrimeField64 {
    const ORDER_U32: u32;

    fn as_canonical_u32(&self) -> u32;

    fn to_unique_u32(&self) -> u32 {
        // A simple default which is optimal for some fields.
        self.as_canonical_u32()
    }
}

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
{
    /// NOTE: This associated type is unbounded. It is originally bounded to `PrimeField`.
    ///       Aeneas doesn't currently support mutually recursive trait delcarations.
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

    fn double(&self) -> Self {
        self.clone() + self.clone()
    }

    fn halve(&self) -> Self {
        // This must be overwritten by PrimeField implementations as this definition
        // is circular when PrimeSubfield = Self. It should also be overwritten by
        // most rings to avoid the multiplication.
        // let half = Self::from_prime_subfield(Self::PrimeSubfield::ONE.halve());
        // self.clone() * half
        self.clone()
    }

    // NOTE: Unimplemented since it's problematic here and it's reimplemented in mersenne31
    fn div_2exp_u64(&self, exp: u64) -> Self; //  {
    //     // Some rings might want to reimplement this to avoid the
    //     // exponentiations (and potentially even the multiplication).
    //     self.clone() * Self::from_prime_subfield(Self::PrimeSubfield::ONE.halve().exp_u64(exp))
    // }
}

// Defined in field/src/integers.rs
pub trait QuotientMap<Int>: Sized {
    fn from_int(int: Int) -> Self;

    fn from_canonical_checked(int: Int) -> Option<Self>;

    unsafe fn from_canonical_unchecked(int: Int) -> Self;
}

pub trait Algebra<F>:
    PrimeCharacteristicRing
    + From<F>
    + Add<F, Output = Self>
    + AddAssign<F>
    + Sub<F, Output = Self>
    + SubAssign<F>
    + Mul<F, Output = Self>
    + MulAssign<F>
{
}

// NOTE: This is problematic at the Charon level
// Every ring is an algebra over itself.
// impl<R: PrimeCharacteristicRing> Algebra<R> for R {}

pub trait Field:
    Algebra<Self>
    // + RawDataSerializable
    // + Packable
    + 'static
    + Copy
    + Div<Self, Output = Self>
    + DivAssign
    + Add<Self::Packing, Output = Self::Packing>
    + Sub<Self::Packing, Output = Self::Packing>
    + Mul<Self::Packing, Output = Self::Packing>
    + Eq
    + Hash
    + Send
    + Sync
    // + Display
    // + Serialize
    // + DeserializeOwned
{
    type Packing; // : PackedField<Scalar = Self>;

    /// A generator of this field's multiplicative group.
    const GENERATOR: Self;

    fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }

    fn is_one(&self) -> bool {
        *self == Self::ONE
    }

    fn try_inverse(&self) -> Option<Self>;

    fn inverse(&self) -> Self {
        self.try_inverse().expect("Tried to invert zero")
    }

    // We're not modelling `add_slices` at the moment
    // fn add_slices(slice_1: &mut [Self], slice_2: &[Self]) {
    //     let (shorts_1, suffix_1) = Self::Packing::pack_slice_with_suffix_mut(slice_1);
    //     let (shorts_2, suffix_2) = Self::Packing::pack_slice_with_suffix(slice_2);
    //     debug_assert_eq!(shorts_1.len(), shorts_2.len());
    //     debug_assert_eq!(suffix_1.len(), suffix_2.len());
    //     for (x_1, &x_2) in shorts_1.iter_mut().zip(shorts_2) {
    //         *x_1 += x_2;
    //     }
    //     for (x_1, &x_2) in suffix_1.iter_mut().zip(suffix_2) {
    //         *x_1 += x_2;
    //     }
    // }

    fn order() -> BigUint;

    fn bits() -> usize {
        Self::order().bits() as usize
    }
}

// NOTE: At the moment we only implement quotient maps for u32, i32 and i64
pub trait PrimeField:
    Field
    + Ord
    // + QuotientMap<u8>
    // + QuotientMap<u16>
    + QuotientMap<u32>
    // + QuotientMap<u64>
    // + QuotientMap<u128>
    // + QuotientMap<usize>
    // + QuotientMap<i8>
    // + QuotientMap<i16>
    + QuotientMap<i32>
    + QuotientMap<i64>
    // + QuotientMap<i128>
    // + QuotientMap<isize>
{
    /// Return the representative of `value` in canonical form
    /// which lies in the range `0 <= x < self.order()`.
    #[must_use]
    fn as_canonical_biguint(&self) -> BigUint;
}
