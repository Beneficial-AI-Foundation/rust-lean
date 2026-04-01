pub const fn gcd_inversion_prime_field_32<const FIELD_BITS: u32>(mut a: u32, mut b: u32) -> i64 {
    const {
        assert!(FIELD_BITS <= 32);
    }
    // debug_assert!(((1_u64 << FIELD_BITS) - 1) >= b as u64);
    assert!(((1_u64 << FIELD_BITS) - 1) >= b as u64);

    // Initialise u, v. Note that |u|, |v| <= 2^0
    let (mut u, mut v) = (1_i64, 0_i64);

    // Let a0 and P denote the initial values of a and b. Observe:
    // `a = u * a0 mod P`
    // `b = v * a0 mod P`
    // `len(a) + len(b) <= 2 * len(P) <= 2 * FIELD_BITS`

    // use manual `while` loop to enable `const`
    let mut i = 0;
    while i < 2 * FIELD_BITS - 2 {
        // Assume at the start of the loop i:
        // (1) `|u|, |v| <= 2^{i}`
        // (2) `2^i * a = u * a0 mod P`
        // (3) `2^i * b = v * a0 mod P`
        // (4) `gcd(a, b) = 1`
        // (5) `b` is odd.
        // (6) `len(a) + len(b) <= max(n - i, 1)`

        if a & 1 != 0 {
            if a < b {
                (a, b) = (b, a);
                (u, v) = (v, u);
            }
            // As b < a, this subtraction cannot increase `len(a) + len(b)`
            a -= b;
            // Observe |u'| = |u - v| <= |u| + |v| <= 2^{i + 1}
            u -= v;

            // As (1) and (2) hold, we have
            // `2^i a' = 2^i * (a - b) = (u - v) * a0 mod P = u' * a0 mod P`
        }
        // As b is odd, a must now be even.
        // This reduces `len(a) + len(b)` by 1 (unless `a = 0` in which case `b = 1` and the sum of the lengths is always 1)
        a >>= 1;

        // Observe |v'| = 2|v| <= 2^{i + 1}
        v <<= 1;

        // Thus as the end of loop i:
        // (1) `|u|, |v| <= 2^{i + 1}`
        // (2) `2^{i + 1} * a = u * a0 mod P`  (As we have halved a)
        // (3) `2^{i + 1} * b = v * a0 mod P`  (As we have doubled v)
        // (4) `gcd(a, b) = 1`
        // (5) `b` is odd.
        // (6) `len(a) + len(b) <= max(n - i - 1, 1)`

        i += 1;
    }

    // After the loops, we see that:
    // |u|, |v| <= 2^{2 * FIELD_BITS - 2}: Hence for FIELD_BITS <= 32 we will not overflow an i64.
    // `2^{2 * FIELD_BITS - 2} * b = v * a0 mod P`
    // `len(a) + len(b) <= 2` with `gcd(a, b) = 1` and `b` odd.
    // This implies that `b` must be `1` and so `v = 2^{2 * FIELD_BITS - 2} a0^{-1} mod P` as desired.
    v
}

/// Given an element x from a 32 bit field F_P compute x/2.
// Originally from field/src/helpers.rs
pub const fn halve_u32<const P: u32>(x: u32) -> u32 {
    let shift = (P + 1) >> 1;
    let half = x >> 1;
    if x & 1 == 0 { half } else { half + shift }
}
