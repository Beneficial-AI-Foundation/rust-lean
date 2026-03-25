/// Arity-2 FRI fold of two evaluations.
///
/// lo = f(x),  hi = f(-x)
/// returns f_folded(x²) = (lo + hi)/2 + β · (lo − hi) · x⁻¹ · (1/2)
///
/// Parameters are field elements mod p (all < p).
/// Caller ensures p is prime, p > 2, and all inputs < p.
pub fn fold_step(
    lo: u64,
    hi: u64,
    beta: u64,
    x_inv: u64,   // multiplicative inverse of x mod p
    two_inv: u64, // multiplicative inverse of 2 mod p
    p: u64,
) -> u64 {
    let sum  = (lo + hi) % p;
    let diff = (lo + p - hi) % p;
    let t    = (diff * x_inv) % p;
    let bt   = (beta * t) % p;
    ((sum + bt) % p * two_inv) % p
}


