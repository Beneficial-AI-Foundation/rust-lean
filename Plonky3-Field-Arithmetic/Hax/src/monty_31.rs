//! An abstraction of 31-bit fields which use a MONTY approach for faster multiplication.

use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign, Not};
use core::marker::PhantomData;
use crate::field::PrimeCharacteristicRing;
use crate::unimplemented::{Iterator, Product, Sum};

////////////////////////////
// IMPORTED FROM utils.rs //
////////////////////////////

// NOTE: Originally form `monty-31/src/utils.rs`
/// Add two integers modulo `P = MP::PRIME`.
///
/// Assumes that `P` is less than `2^31` and `a + b <= 2P` for all array pairs `a, b`.
/// If the inputs are not in this range, the result may be incorrect.
/// The result will be in the range `[0, P]` and equal to `(a + b) mod P`.
/// It will be equal to `P` if and only if `a + b = 2P` so provided `a + b < 2P`
/// the result is guaranteed to be less than `P`.
#[inline]
#[must_use]
pub(crate) const fn add<MP: MontyParameters>(lhs: u32, rhs: u32) -> u32 {
    let mut sum = lhs + rhs;
    let (corr_sum, over) = sum.overflowing_sub(MP::PRIME);
    if !over {
        sum = corr_sum;
    }
    sum
}

// NOTE: Originally form `monty-31/src/utils.rs`
/// Subtract two integers modulo `P = MP::PRIME`.
///
/// Assumes that `P` is less than `2^31` and `|a - b| <= P` for all array pairs `a, b`.
/// If the inputs are not in this range, the result may be incorrect.
/// The result will be in the range `[0, P]` and equal to `(a - b) mod P`.
/// It will be equal to `P` if and only if `a - b = P` so provided `a - b < P`
/// the result is guaranteed to be less than `P`.
#[inline]
#[must_use]
pub(crate) const fn sub<MP: MontyParameters>(lhs: u32, rhs: u32) -> u32 {
    let (mut diff, over) = lhs.overflowing_sub(rhs);
    let corr = if over { MP::PRIME } else { 0 };
    diff = diff.wrapping_add(corr);
    diff
}

// NOTE: Originally form `monty-31/src/utils.rs`
/// Given an element `x` from a 31 bit field `F` compute `x/2`.
/// The input must be in `[0, P)`.
/// The output will also be in `[0, P)`.
#[inline]
pub(crate) const fn halve_u32<FP: FieldParameters>(input: u32) -> u32 {
    let shr = input >> 1;
    let lo_bit = input & 1;
    let shr_corr = shr + FP::HALF_P_PLUS_1;
    if lo_bit == 0 { shr } else { shr_corr }
}

// NOTE: Originally form `monty-31/src/utils.rs`
/// Convert a u32 into MONTY form.
/// There are no constraints on the input.
/// The output will be a u32 in range `[0, P)`.
#[inline]
pub(crate) const fn to_monty<MP: MontyParameters>(x: u32) -> u32 {
    (((x as u64) << MP::MONTY_BITS) % MP::PRIME as u64) as u32
}

// NOTE: Originally form `monty-31/src/utils.rs`
/// Montgomery reduction of a value in `0..P << MONTY_BITS`.
///
/// The input must be in `[0, MONTY * P)`.
/// The output will be in `[0, P)`.
#[inline]
#[must_use]
pub(crate) const fn monty_reduce<MP: MontyParameters>(x: u64) -> u32 {
    // t = x * MONTY_MU mod MONTY
    let t = x.wrapping_mul(MP::MONTY_MU as u64) & (MP::MONTY_MASK as u64);

    // u = t * P
    let u = t * (MP::PRIME as u64);

    // Thus:
    // 1. x - u = x - t * P = x mod P
    // 2. x - u = x - x * MONTY_MU * P mod MONTY = 0 mod MONTY
    // For the second point note that MONTY_MU = P^{-1} mod MONTY.

    // Additionally, u < MONTY * P so: - MONTY * P < x - u < MONTY * P
    // Thus after dividing by MONTY, -P < (x - u)/MONTY < P.
    // So we can just add P to the result if it is negative.

    let (x_sub_u, over) = x.overflowing_sub(u);
    let x_sub_u_hi = (x_sub_u >> MP::MONTY_BITS) as u32;
    let corr = if over { MP::PRIME } else { 0 };
    x_sub_u_hi.wrapping_add(corr)
}

// NOTE: Originally form `monty-31/src/utils.rs`
/// Convert a u32 out of MONTY form.
/// There are no constraints on the input.
/// The output will be a u32 in range `[0, P)`.
#[inline]
#[must_use]
pub(crate) const fn from_monty<MP: MontyParameters>(x: u32) -> u32 {
    monty_reduce::<MP>(x as u64)
}

//////////////////////////////////
// IMPORTED FROM data_traits.rs //
//////////////////////////////////

// NOTE: Originally form `monty-31/src/data_traits.rs`
// Missing supertraits: Debug + Hash
/// MontyParameters contains the prime P along with constants needed to convert elements into and out of MONTY form.
/// The MONTY constant is assumed to be a power of 2.
pub trait MontyParameters:
    Copy + Default // + Eq //+ PartialEq //+ Sync + Send + 'static
{
    // A 31-bit prime.
    const PRIME: u32;

    // The log_2 of our MONTY constant.
    const MONTY_BITS: u32;

    // We define MONTY_MU = PRIME^-1 (mod 2^MONTY_BITS). This is different from the usual convention
    // (MONTY_MU = -PRIME^-1 (mod 2^MONTY_BITS)) but it avoids a carry.
    const MONTY_MU: u32;

    const MONTY_MASK: u32 = ((1u64 << Self::MONTY_BITS) - 1) as u32;
}

// NOTE: Originally form `monty-31/src/data_traits.rs`
/// FieldParameters contains constants and methods needed to imply PrimeCharacteristicRing, Field and PrimeField32 for MontyField31.
pub trait FieldParameters: PackedMontyParameters + Sized {
    // Simple field constants.
    const MONTY_ZERO: MontyField31<Self> = MontyField31::new(0);
    const MONTY_ONE: MontyField31<Self> = MontyField31::new(1);
    const MONTY_TWO: MontyField31<Self> = MontyField31::new(2);
    const MONTY_NEG_ONE: MontyField31<Self> = MontyField31::new(Self::PRIME - 1);

    // A generator of the fields multiplicative group. Needs to be given in Monty Form.
    const MONTY_GEN: MontyField31<Self>;

    const HALF_P_PLUS_1: u32 = (Self::PRIME + 1) >> 1;
}

// NOTE: Originally form `monty-31/src/data_traits.rs`
/// PackedMontyParameters contains constants needed for MONTY operations for packings of Monty31 fields.
pub trait PackedMontyParameters: MontyParameters {}

///////////////////////////////
// IMPORTED FROM monty_31.rs //
///////////////////////////////

#[derive(Clone, Copy, Default, Eq, Hash, PartialEq)]
// #[repr(transparent)] // Important for reasoning about memory layout.
// #[must_use]
pub struct MontyField31<MP: MontyParameters> {
    /// The MONTY form of the field element, saved as a positive integer less than `P`.
    ///
    /// This is `pub(crate)` for tests and delayed reduction strategies. If you're accessing `value` outside of those, you're
    /// likely doing something fishy.
    pub(crate) value: u32,
    _phantom: PhantomData<MP>,
}

impl<MP: MontyParameters> MontyField31<MP> {
    /// Create a new field element from any `u32`.
    ///
    /// Any `u32` value is accepted and automatically converted to Montgomery form.
    #[inline(always)]
    pub const fn new(value: u32) -> Self {
        Self {
            value: to_monty::<MP>(value),
            _phantom: PhantomData,
        }
    }

    /// Create a new field element from something already in MONTY form.
    /// This is `pub(crate)` for tests and delayed reduction strategies. If you're using it outside of those, you're
    /// likely doing something fishy.
    #[inline(always)]
    pub(crate) const fn new_monty(value: u32) -> Self {
        Self {
            value,
            _phantom: PhantomData,
        }
    }

    /// Produce a u32 in range [0, P) from a field element corresponding to the true value.
    #[inline(always)]
    pub(crate) const fn to_u32(elem: &Self) -> u32 {
        from_monty::<MP>(elem.value)
    }

    /// Convert a `[u32; N]` array to an array of field elements.
    ///
    /// Const version of `input.map(MontyField31::new)`.
    #[inline]
    pub const fn new_array<const N: usize>(input: [u32; N]) -> [Self; N] {
        let mut output = [Self::new_monty(0); N];
        let mut i = 0;
        while i < N {
            output[i] = Self::new(input[i]);
            i += 1;
        }
        output
    }

    /// Convert a constant 2d u32 array into a constant 2d array of field elements.
    /// Constant version of array.map(MontyField31::new_array).
    #[inline]
    pub const fn new_2d_array<const N: usize, const M: usize>(
        input: [[u32; N]; M],
    ) -> [[Self; N]; M] {
        let mut output = [[Self::new_monty(0); N]; M];
        let mut i = 0;
        while i < M {
            output[i] = Self::new_array(input[i]);
            i += 1;
        }
        output
    }
}

impl<FP: FieldParameters> PrimeCharacteristicRing for MontyField31<FP> {
    type PrimeSubfield = Self;

    const ZERO: Self = FP::MONTY_ZERO;
    const ONE: Self = FP::MONTY_ONE;
    const TWO: Self = FP::MONTY_TWO;
    const NEG_ONE: Self = FP::MONTY_NEG_ONE;

    #[inline(always)]
    fn from_prime_subfield(f: Self) -> Self {
        f
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::new_monty(halve_u32::<FP>(self.value))
    }
}

impl<FP: MontyParameters> Add for MontyField31<FP> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self::new_monty(add::<FP>(self.value, rhs.value))
    }
}

impl<FP: MontyParameters> Sub for MontyField31<FP> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self::new_monty(sub::<FP>(self.value, rhs.value))
    }
}

impl<FP: FieldParameters> Neg for MontyField31<FP> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Self::ZERO - self
    }
}

impl<FP: MontyParameters> Mul for MontyField31<FP> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let long_prod = self.value as u64 * rhs.value as u64;
        Self::new_monty(monty_reduce::<FP>(long_prod))
    }
}

// AddAssign is implemented via the `impl_add_assign` macro
// Source: field/src/op_assign_macros.rs
impl<FP: FieldParameters> AddAssign for MontyField31<FP> {
    fn add_assign(&mut self, rhs: MontyField31<FP>) {
        *self = *self + rhs.into();
    }
}

// SubAssign is implemented via the `impl_sub_assign` macro
// Source: field/src/op_assign_macros.rs
impl<FP: FieldParameters> SubAssign for MontyField31<FP> {
    fn sub_assign(&mut self, rhs: MontyField31<FP>) {
        *self = *self - rhs.into();
    }
}

// MulAssign is implemented via the `impl_mul_assign` macro
// Source: field/src/op_assign_macros.rs
impl<FP: FieldParameters> MulAssign for MontyField31<FP> {
    fn mul_assign(&mut self, rhs: MontyField31<FP>) {
        *self = *self * rhs.into();
    }
}

/// NOTE: Placeholder dummy impl
impl<FP: FieldParameters> Product for MontyField31<FP> {
    // Original:
    // fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    //     iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
    // }
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self::new(0)
    }
}

impl<FP: FieldParameters> Sum for MontyField31<FP> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self::new(0)
    }
}
