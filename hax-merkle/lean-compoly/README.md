# Horner algorithm verification (WIP) using CompPoly

This folder documents an ongoing experiment toward an end-to-end verification workflow:

**Rust implementation → hax extraction → CompPoly specification → Lean proofs**

This repository follows a “one repo, multiple PoCs” approach. The Horner PoC currently lives in:
- rust/horner_eval_rs/ — Rust implementation to be extracted with hax
- lean-compoly/ — Lean project intended to host CompPoly specs and (eventually) proofs for the extracted code

Status note: this work is **in progress**. At the moment, the hax-extracted Horner code does not compile in the same Lean project as CompPoly due to Lean toolchain version pinning across libraries. The primary success so far is that we raised issues and coordinated with maintainers, who agreed on a unified Lean version. Once the upgrades land, the pipeline should become feasible without splitting projects.


## Horner Evaluation

Many zk proof systems (including Plonky3-based stacks) rely heavily on polynomial arithmetic. A minimal but representative component is **univariate polynomial evaluation**.

Given coefficients [c0, c1, c2, …], Horner’s method computes:
p(x)=c0+x(c1+x(c2+… ))

We aim to verify that the Rust implementation of Horner evaluation corresponds to a mathematical specification expressed using **CompPoly**.

**Reference (algorithmic origin)**

We use Plonky3-recursion as the [Plonky3-recursion](https://github.com/Plonky3/Plonky3-recursion/blob/d3ccaf73d5f707b4a2018ac65ece55d329fee934/recursion/src/pcs/fri/verifier.rs#L98).


```Rust
fn evaluate_polynomial<EF: Field>(
    builder: &mut CircuitBuilder<EF>,
    coefficients: &[Target],
    point: Target,
) -> Target {
    let mut result = coefficients[coefficients.len() - 1];
    for &coeff in coefficients.iter().rev().skip(1) {
        result = builder.mul(result, point);
        result = builder.add(result, coeff);
    }
    result
}
```

This is Horner evaluation, but implemented over a circuit builder abstraction. For a first PoC we extract a simpler arithmetic-only version.

## Rust side (implementation + extraction target)

**Create an extraction-friendly Rust crate**

```bash
cd zkvm-merkle-lean-verified/rust
cargo new --lib horner_eval_rs
cd horner_eval_rs
cargo add --target 'cfg(hax)' --git https://github.com/hacspec/hax hax-lib

```

**Extraction-friendly Horner implementation**

Because the hax Lean backend is still evolving (and iterator support is limited), we avoid Rust iterators and write the loop using while. This keeps the algorithm identical but reduces extraction complexity.

```Rust
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
```

**Run hax extraction**

We extract to:
- lean-compoly/CompPolyEval/Extracted/Horner_eval_rs.lean

For convenience we added a script:
- scripts/extract_horner_to_compoly.sh

## Lean side (CompPoly specification)

We created a separate Lean project:

- lean-compoly/

and added CompPoly as a dependency.

**Specification module**

We added:

- lean-compoly/CompPolyEval/Spec.lean

This defines a univariate polynomial model (one variable) over ℤ using CompPoly:

- P := CPoly.CMvPolynomial 1 ℤ
- X0 as the variable X in one dimension
- polyOfCoeffs : List ℤ → P building the polynomial from coefficients
- evalAt : ℤ → P → ℤ using CPoly.CMvPolynomial.eval

This enables a clean mathematical statement of Horner correctness in Lean once the extracted code can be compiled in the same environment.

## Proof plan (WIP)

A direct equivalence proof between the extracted Rust function and the CompPoly spec over ℤ will require:

- Panic/exception freedom (or bounds assumptions) for the extracted i64 code, since the hax Lean model uses RustM and overflow-aware operators.
- A semantic bridge from machine integers (i64) to mathematical integers (ℤ), typically under bounds that rule out overflow.
- The main functional correctness theorem: extracted Horner evaluation equals evalAt of polyOfCoeffs.

## Current bottleneck: Lean toolchain version mismatch

At the time of writing, the blocker for a single-project end-to-end pipeline is Lean version pinning across libraries:

- hax Lean prelude was pinned to a single Lean version and is sensitive to Lean changes.
- CompPoly and ArkLib were pinned to different Lean versions.

This prevented compiling the hax-extracted Horner module in the same Lean project as CompPoly.

### Coordination outcome (major progress)

As a result of issues raised during this work, maintainers of hax, CompPoly, and ArkLib agreed to converge on a unified Lean toolchain version:

**Lean 4.26.0**

Once these upgrades land, we expect the end-to-end pipeline:

**Rust → hax → CompPoly spec → proofs**

to become feasible without splitting across incompatible Lean versions.

Reference discussion: hax issue [#1873](https://github.com/cryspen/hax/issues/1873)

## Artifacts in this repository

- rust/horner_eval_rs/ — Rust Horner implementation (tests pass)
- scripts/extract_horner_to_compoly.sh — extraction helper
- lean-compoly/CompPolyEval/Spec.lean — CompPoly-based specification (typechecks)
- lean-compoly/CompPolyEval/Extracted/Horner_eval_rs.lean — hax-extracted Lean code (generated; compilation depends on toolchain alignment)

## Next steps

- Update dependencies once hax/CompPoly/ArkLib are on Lean 4.26.0.
- Compile extracted Horner code and write the first proof obligations:
    - panic-freedom / bounds,
    - correctness w.r.t. CompPoly eval.
- Add additional normalization lemmas/tactics (simp/grind sets) as needed to support proof automation for Horner and future polynomial components.
