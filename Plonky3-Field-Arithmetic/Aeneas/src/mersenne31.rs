use crate::field::{
    Algebra, Field, PrimeCharacteristicRing, PrimeField, PrimeField32, PrimeField64, QuotientMap,
};
use crate::util::{gcd_inversion_prime_field_32, halve_u32};
use crate::mocks::{Hash, Hasher};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use num_bigint::BigUint;

#[allow(dead_code)]

/// The Mersenne31 prime
const P: u32 = (1 << 31) - 1;

/// The prime field `F_p` where `p = 2^31 - 1`.
#[derive(Copy, Clone, Default)]
#[repr(transparent)] // Important for reasoning about memory layout.
#[must_use]
pub struct Mersenne31 {
    /// Not necessarily canonical, but must fit in 31 bits.
    pub(crate) value: u32,
}

impl Mersenne31 {
    /// Create a new field element from any `u32`.
    ///
    /// Any `u32` value is accepted and automatically reduced modulo P.
    #[inline]
    pub const fn new(value: u32) -> Self {
        Self { value: value % P }
    }

    /// Create a field element from a value assumed to be < 2^31.
    ///
    /// # Safety
    /// The element must lie in the range: `[0, 2^31 - 1]`.
    #[inline]
    pub(crate) const fn new_reduced(value: u32) -> Self {
        //debug_assert!((value >> 31) == 0);
        assert!((value >> 31) == 0);
        Self { value }
    }

    /// Convert a u32 element into a Mersenne31 element.
    ///
    /// Returns `None` if the element does not lie in the range: `[0, 2^31 - 1]`.
    #[inline]
    pub const fn new_checked(value: u32) -> Option<Self> {
        if (value >> 31) == 0 {
            Some(Self { value })
        } else {
            None
        }
    }

    // NOTE: We comment this out temporarily until we set on loops
    // /// Convert a `[u32; N]` array to an array of field elements.
    // ///
    // /// Const version of `input.map(Mersenne31::new)`.
    // #[inline]
    // pub const fn new_array<const N: usize>(input: [u32; N]) -> [Self; N] {
    //     let mut output = [Self::ZERO; N];
    //     let mut i = 0;
    //     while i < N {
    //         output[i].value = input[i] % P;
    //         i += 1;
    //     }
    //     output
    // }
}

impl PrimeCharacteristicRing for Mersenne31 {
    type PrimeSubfield = Self;

    const ZERO: Self = Self { value: 0 };
    const ONE: Self = Self { value: 1 };
    const TWO: Self = Self { value: 2 };
    const NEG_ONE: Self = Self {
        value: Self::ORDER_U32 - 1,
    };

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f
    }

    #[inline]
    fn from_bool(b: bool) -> Self {
        Self::new_reduced(b as u32)
    }

    #[inline]
    fn halve(&self) -> Self {
        // In a Mersenne field, division by 2 is a right rotation by 1 bit.
        Self::new_reduced(halve_u32::<P>(self.value))
    }

    #[inline]
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, multiplication by 2^k is just a left rotation by k bits.
        let exp = exp % 31;
        let left = (self.value << exp) & ((1 << 31) - 1);
        let right = self.value >> (31 - exp);
        let rotated = left | right;
        Self::new_reduced(rotated)
    }

    #[inline]
    fn div_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, division by 2^k is just a right rotation by k bits.
        let exp = (exp % 31) as u8;
        let left = self.value >> exp;
        let right = (self.value << (31 - exp)) & ((1 << 31) - 1);
        let rotated = left | right;
        Self::new_reduced(rotated)
    }
}

///////////////////////////
// FIELD IMPLEMENTATIONS //
///////////////////////////

// NOTE: This is a workaround because Charon complains about
impl Algebra<Mersenne31> for Mersenne31 {}

impl Field for Mersenne31 {
    type Packing = Self;

    // Sage: GF(2^31 - 1).multiplicative_generator()
    const GENERATOR: Self = Self::new(7);

    fn is_zero(&self) -> bool {
        self.value == 0 || self.value == Self::ORDER_U32
    }

    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        // Number of bits in the Mersenne31 prime.
        const NUM_PRIME_BITS: u32 = 31;

        // gcd_inversion returns the inverse multiplied by 2^60 so we need to correct for that.
        let inverse_i64 = gcd_inversion_prime_field_32::<NUM_PRIME_BITS>(self.value, P);
        Some(Self::from_int(inverse_i64).div_2exp_u64(60))
    }

    fn order() -> BigUint {
        P.into()
    }
}

/// NOTE: Dummy implementation of a dummy trait
impl PrimeField64 for Mersenne31 {
    const ORDER_U64: u64 = <Self as PrimeField32>::ORDER_U32 as u64;

    fn as_canonical_u64(&self) -> u64 {
        self.as_canonical_u32().into()
    }
}

/// NOTE: Dummy implementation of a dummy trait
impl PrimeField32 for Mersenne31 {
    const ORDER_U32: u32 = P;
    fn as_canonical_u32(&self) -> u32 {
        // Since our invariant guarantees that `value` fits in 31 bits, there is only one possible
        // `value` that is not canonical, namely 2^31 - 1 = p = 0.
        if self.value == Self::ORDER_U32 {
            0
        } else {
            self.value
        }
    }
}

impl PrimeField for Mersenne31 {
    fn as_canonical_biguint(&self) -> BigUint {
        <Self as PrimeField32>::as_canonical_u32(self).into()
    }
}

////////////////////////////////
// ARITHMETIC IMPLEMENTATIONS //
////////////////////////////////

impl Add for Mersenne31 {
    type Output = Self;

    // #[inline]
    fn add(self, rhs: Self) -> Self {
        // See the following for a way to compute the sum that avoids
        // the conditional which may be preferable on some
        // architectures.
        // https://github.com/Plonky3/Plonky3/blob/6049a30c3b1f5351c3eb0f7c994dc97e8f68d10d/mersenne-31/src/lib.rs#L249

        // Working with i32 means we get a flag which informs us if overflow happened.
        let (sum_i32, over) = (self.value as i32).overflowing_add(rhs.value as i32);
        let sum_u32 = sum_i32 as u32;
        let sum_corr = sum_u32.wrapping_sub(Self::ORDER_U32);

        // If self + rhs did not overflow, return it.
        // If self + rhs overflowed, sum_corr = self + rhs - (2**31 - 1).
        Self::new_reduced(if over { sum_corr } else { sum_u32 })
    }
}

// AddAssign is implemented via the `impl_add_assign` macro
// Source: field/src/op_assign_macros.rs
impl AddAssign for Mersenne31 {
    fn add_assign(&mut self, rhs: Mersenne31) {
        *self = *self + rhs.into();
    }
}

impl Sub for Mersenne31 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        // NOTE: Removed because of Hax not translating `overflowing_sub`
        let (mut sub, over) = self.value.overflowing_sub(rhs.value);

        // If we didn't overflow we have the correct value.
        // Otherwise we have added 2**32 = 2**31 + 1 mod 2**31 - 1.
        // Hence we need to remove the most significant bit and subtract 1.
        sub -= over as u32;
        Self::new_reduced(sub & Self::ORDER_U32)
    }
}

// SubAssign is implemented via the `impl_sub_assign` macro
// Source: field/src/op_assign_macros.rs
impl SubAssign for Mersenne31 {
    fn sub_assign(&mut self, rhs: Mersenne31) {
        *self = *self - rhs.into();
    }
}

impl Mul for Mersenne31 {
    type Output = Self;

    // #[inline]
    // #[allow(clippy::cast_possible_truncation)]
    fn mul(self, rhs: Self) -> Self {
        let prod = u64::from(self.value) * u64::from(rhs.value);
        from_u62(prod)
    }
}

// MulAssign is implemented via the `impl_mul_assign` macro
// Source: field/src/op_assign_macros.rs
impl MulAssign for Mersenne31 {
    fn mul_assign(&mut self, rhs: Mersenne31) {
        *self = *self * rhs.into();
    }
}

// Div is implemented via the `impl_div_methods` macro
// Source: field/src/op_assign_macros.rs
impl Div<Mersenne31> for Mersenne31 {
    type Output = Self;
    fn div(self, rhs: Mersenne31) -> Self {
        self * Self::from(rhs.inverse())
    }
}

// Div is implemented via the `impl_div_methods` macro
// Source: field/src/op_assign_macros.rs
impl DivAssign for Mersenne31 {
    fn div_assign(&mut self, rhs: Mersenne31) {
        *self *= Self::from(rhs.inverse());
    }
}

impl Neg for Mersenne31 {
    type Output = Self;

    // #[inline]
    fn neg(self) -> Self::Output {
        // Can't underflow, since self.value is 31-bits and thus can't exceed ORDER.
        Self::new_reduced(Self::ORDER_U32 - self.value)
    }
}

pub(crate) fn from_u62(input: u64) -> Mersenne31 {
    // debug_assert!(input < (1 << 62));
    assert!(input < (1 << 62));
    let input_lo = (input & ((1 << 31) - 1)) as u32;
    let input_high = (input >> 31) as u32;
    Mersenne31::new_reduced(input_lo) + Mersenne31::new_reduced(input_high)
}

////////////////////////////////////////
// EQUALITY AND ORDER IMPLEMENTATIONS //
////////////////////////////////////////

impl PartialEq for Mersenne31 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_canonical_u32() == other.as_canonical_u32()
    }
}

impl Eq for Mersenne31 {}

// impl Packable for Mersenne31 {}

impl Hash for Mersenne31 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.to_unique_u32());
    }
}

impl Ord for Mersenne31 {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_canonical_u32().cmp(&other.as_canonical_u32())
    }
    // NOTE: Copied `max`, `min` and `clamp` since Aeneas
    //       is not extracting them from the trait
    fn max(self, other: Self) -> Self
    // where
    //     Self: Sized + [const] std::marker::Destruct,
    {
        if other < self { self } else { other }
    }
    fn min(self, other: Self) -> Self
    where
        // Self: Sized + [const] std::marker::Destruct,
    {
        if other < self { other } else { self }
    }
    fn clamp(self, min: Self, max: Self) -> Self
    where
        // Self: Sized + [const] std::marker::Destruct,
    {
        assert!(min <= max);
        assert!(max >= min); // Added here so that Aeneas produces `ge`
        if self < min {
            min
        } else if self > max {
            max
        } else {
            self
        }
    }
}

impl PartialOrd for Mersenne31 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

//////////////////////////////////
// QUOTIENT MAPS IMPLEMENTATION //
//////////////////////////////////

// NOTE: At the moment we only implement `QuotientMap` for u32, i32, u64 and i64

impl QuotientMap<u32> for Mersenne31 {
    #[inline]
    fn from_int(int: u32) -> Self {
        // To reduce `n` to 31 bits, we clear its MSB, then add it back in its reduced form.
        let msb = int & (1 << 31);
        let msb_reduced = msb >> 31;
        Self::new_reduced(int ^ msb) + Self::new_reduced(msb_reduced)
    }

    fn from_canonical_checked(int: u32) -> Option<Self> {
        (int < Self::ORDER_U32).then(|| Self::new_reduced(int))
    }

    unsafe fn from_canonical_unchecked(int: u32) -> Self {
        // debug_assert!(int < Self::ORDER_U32);
        assert!(int < Self::ORDER_U32);
        Self::new_reduced(int)
    }
}

impl QuotientMap<i32> for Mersenne31 {
    #[inline]
    fn from_int(int: i32) -> Self {
        if int >= 0 {
            Self::new_reduced(int as u32)
        } else if int > (-1 << 31) {
            Self::new_reduced(Self::ORDER_U32.wrapping_add_signed(int))
        } else {
            // The only other option is int = -(2^31) = -1 mod p.
            Self::NEG_ONE
        }
    }

    #[inline]
    fn from_canonical_checked(int: i32) -> Option<Self> {
        const TWO_EXP_30: i32 = 1 << 30;
        const NEG_TWO_EXP_30_PLUS_1: i32 = (-1 << 30) + 1;
        match int {
            0..TWO_EXP_30 => Some(Self::new_reduced(int as u32)),
            NEG_TWO_EXP_30_PLUS_1..0 => {
                Some(Self::new_reduced(Self::ORDER_U32.wrapping_add_signed(int)))
            }
            _ => None,
        }
    }

    #[inline(always)]
    unsafe fn from_canonical_unchecked(int: i32) -> Self {
        if int >= 0 {
            Self::new_reduced(int as u32)
        } else {
            Self::new_reduced(Self::ORDER_U32.wrapping_add_signed(int))
        }
    }
}

impl QuotientMap<u64> for Mersenne31 {
    /// Convert a given `u64` integer into an element of the `Mersenne31` field.
    ///
    /// Uses a modular reduction to reduce to canonical form.
    /// This should be avoided in performance critical locations.
    #[inline]
    fn from_int(int: u64) -> Mersenne31 {
        // Check at compile time.
        const {
            assert!(size_of::<u64>() > size_of::<u32>());
        }
        let red = (int % (Mersenne31::ORDER_U32 as u64)) as u32;
        unsafe {
            // This is safe as red is less than the field order by assumption.
            Self::from_canonical_unchecked(red)
        }
    }

    /// Convert a given `u64` integer into an element of the `Mersenne31` field.
    ///
    /// Returns `None` if the input does not lie in the range: [0, 2^31 - 2].
    #[inline]
    fn from_canonical_checked(int: u64) -> Option<Mersenne31> {
        if int < Mersenne31::ORDER_U32 as u64 {
            unsafe {
                // This is safe as we just checked that int is less than the field order.
                Some(Self::from_canonical_unchecked(int as u32))
            }
        } else {
            None
        }
    }

    /// Convert a given `u64` integer into an element of the `Mersenne31` field.
    ///
    /// # Safety
    /// The input must lie in the range:", [0, 2^31 - 1].
    #[inline]
    unsafe fn from_canonical_unchecked(int: u64) -> Mersenne31 {
        unsafe { Self::from_canonical_unchecked(int as u32) }
    }
}

impl QuotientMap<i64> for Mersenne31 {
    /// Convert a given `i64` integer into an element of the `Mersenne31` field.
    ///
    /// This checks the sign and then makes use of the equivalent method for unsigned integers.
    /// This should be avoided in performance critical locations.
    #[inline]
    fn from_int(int: i64) -> Mersenne31 {
        if int >= 0 {
            Self::from_int(int as u64)
        } else {
            -Self::from_int(-int as u64)
        }
    }

    /// Convert a given `i64` integer into an element of the `Mersenne31` field.
    ///
    /// Returns `None` if the input does not lie in the range: `[-2^30, 2^30]`.
    #[inline]
    fn from_canonical_checked(int: i64) -> Option<Mersenne31> {
        // We just check that int fits into an i32 now and then use the i32 method.
        let int_small = TryInto::<i32>::try_into(int);
        if int_small.is_ok() {
            Self::from_canonical_checked(int_small.unwrap())
        } else {
            None
        }
    }

    /// Convert a given `i64` integer into an element of the `Mersenne31` field.
    ///
    /// # Safety
    /// The input must lie in the range:", `[1 - 2^31, 2^31 - 1]`.
    #[inline]
    unsafe fn from_canonical_unchecked(int: i64) -> Mersenne31 {
        unsafe { Self::from_canonical_unchecked(int as i32) }
    }
}
