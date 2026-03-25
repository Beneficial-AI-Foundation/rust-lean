use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use crate::field::{PrimeCharacteristicRing, PrimeField64, PrimeField32};
use crate::unimplemented::*;

/// The Mersenne31 prime
const P: u32 = (1 << 31) - 1;
/// The Mersenne31 prime as u64 to avoid casting `P`
const P64: u64 = (1 << 31) - 1;

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

    /// Convert a `[u32; N]` array to an array of field elements.
    ///
    /// Const version of `input.map(Mersenne31::new)`.
    #[inline]
    pub const fn new_array<const N: usize>(input: [u32; N]) -> [Self; N] {
        let mut output = [Self::ZERO; N];
        let mut i = 0;
        while i < N {
            output[i].value = input[i] % P;
            i += 1;
        }
        output
    }
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

}

////////////////////////////////
// ARITHMETIC IMPLEMENTATIONS //
////////////////////////////////

/// NOTE: Dummy implementation of a dummy trait
impl PrimeField64 for Mersenne31 {
    // const ORDER_U64: u64 = <Self as PrimeField32>::ORDER_U32 as u64;
    const ORDER_U64 : u64 = P64;

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

impl Add for Mersenne31 {
    type Output = Self;

    // #[inline]
    fn add(self, rhs: Self) -> Self {
        // See the following for a way to compute the sum that avoids
        // the conditional which may be preferable on some
        // architectures.
        // https://github.com/Plonky3/Plonky3/blob/6049a30c3b1f5351c3eb0f7c994dc97e8f68d10d/mersenne-31/src/lib.rs#L249

        // NOTE: Removed because of Hax not translating `overflowing_add` and `wrapping_sub`
        // Working with i32 means we get a flag which informs us if overflow happened.
        let (sum_i32, over) = (self.value as i32).overflowing_add(rhs.value as i32);
        let sum_u32 = sum_i32 as u32;
        let sum_corr = sum_u32.wrapping_sub(Self::ORDER_U32);

        // If self + rhs did not overflow, return it.
        // If self + rhs overflowed, sum_corr = self + rhs - (2**31 - 1).
        Self::new_reduced(if over { sum_corr } else { sum_u32 })
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

impl Neg for Mersenne31 {
    type Output = Self;

    // #[inline]
    fn neg(self) -> Self::Output {
        // Can't underflow, since self.value is 31-bits and thus can't exceed ORDER.
        Self::new_reduced(Self::ORDER_U32 - self.value)
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

// AddAssign is implemented via the `impl_add_assign` macro
// Source: field/src/op_assign_macros.rs
impl AddAssign for Mersenne31 {
    fn add_assign(&mut self, rhs: Mersenne31) {
        *self = *self + rhs.into();
    }
}

// SubAssign is implemented via the `impl_sub_assign` macro
// Source: field/src/op_assign_macros.rs
impl SubAssign for Mersenne31 {
    fn sub_assign(&mut self, rhs: Mersenne31) {
        *self = *self - rhs.into();
    }
}

// MulAssign is implemented via the `impl_mul_assign` macro
// Source: field/src/op_assign_macros.rs
impl MulAssign for Mersenne31 {
    fn mul_assign(&mut self, rhs: Mersenne31) {
        *self = *self * rhs.into();
    }
}

/// NOTE: Placeholder dummy impl
impl Sum for Mersenne31 {
    // #[inline]
    // fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    //     // This is faster than iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO) for iterators of length >= 6.
    //     // It assumes that iter.len() < 2^31.

    //     // This sum will not overflow so long as iter.len() < 2^33.
    //     let sum = iter.map(|x| x.value as u64).sum::<u64>();

    //     // sum is < 2^62 provided iter.len() < 2^31.
    //     from_u62(sum)
    // }
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self::new(0)
    }
}

/// NOTE: Placeholder dummy impl. Unclear atm where the source is.
impl Product for Mersenne31 {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self::new(0)
    }
}

pub(crate) fn from_u62(input: u64) -> Mersenne31 {
    // debug_assert!(input < (1 << 62));
    assert!(input < (1 << 62));
    let input_lo = (input & ((1 << 31) - 1)) as u32;
    let input_high = (input >> 31) as u32;
    Mersenne31::new_reduced(input_lo) + Mersenne31::new_reduced(input_high)
}
