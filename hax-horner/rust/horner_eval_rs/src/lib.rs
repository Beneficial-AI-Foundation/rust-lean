fn horner_rec(coeffs: &[i64], x: i64, i: usize, acc: i64) -> i64 {
    if i == 0 {
        acc
    } else {
        // i > 0
        let i1 = i - 1;
        let acc1 = acc * x + coeffs[i1];
        horner_rec(coeffs, x, i1, acc1)
    }
}

pub fn horner_eval_i64(coeffs: &[i64], x: i64) -> i64 {
    if coeffs.is_empty() {
        return 0;
    }
    let n = coeffs.len();
    // start from highest coefficient
    horner_rec(coeffs, x, n - 1, coeffs[n - 1])
}
