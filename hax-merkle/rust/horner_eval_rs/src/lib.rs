pub fn horner_eval_i64(coeffs: &[i64], x: i64) -> i64 {
    // p(x) = a0 + a1*x + ... + an*x^n
    // Horner: (((an*x + a_{n-1})*x + ...)*x + a0)
    if coeffs.is_empty() {
        return 0;
    }

    let mut i = coeffs.len();
    let mut acc = coeffs[i - 1];

    while i > 1 {
        i -= 1;
        acc = acc * x + coeffs[i - 1];
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn horner_basic() {
        // p(x) = 3 + 2x + x^2, x=10 => 3 + 20 + 100 = 123
        let coeffs = [3i64, 2i64, 1i64];
        assert_eq!(horner_eval_i64(&coeffs, 10), 123);
    }

    #[test]
    fn empty_is_zero() {
        let coeffs: [i64; 0] = [];
        assert_eq!(horner_eval_i64(&coeffs, 7), 0);
    }
}
