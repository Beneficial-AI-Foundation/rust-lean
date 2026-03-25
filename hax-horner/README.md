## Horner evaluation function from Plonky3: PoC‑project Hax → CompPoly spec → proofs 

Lake/CompPoly/Hax - can be built together for Lean 4.26.0, using hax from PR [#1880](https://github.com/cryspen/hax/pull/1880) (which not merged yet)

But this pipeline is having patches:

0) we had to change initial Rust code
1) we fill Hax's Core_models locally
2) we patch generated Lean (partial def for termination). opened issue [#1882](https://github.com/cryspen/hax/issues/1882)

we are not able to prove full correctness relative to ℤ without assumptions (panic-free + no overflow + i64→ℤ bridge)

But we have pipeline with minimal PoC proof 

## Rust Code preparation for extraction

Function to verify: [Horner Evaluation](Verificahttps://github.com/Plonky3/Plonky3-recursion/blob/d3ccaf73d5f707b4a2018ac65ece55d329fee934/recursion/src/pcs/fri/verifier.rs#L98) 

we replaced iterators with while loop, but we couldn't compile extracted file (hax wouldn't translate it yet: missing invariants for the while_loop). 

while_loop triggers VC generation / invariants in Lean backend, recursion triggers termination; we chose recursion + partial def patch for PoC

so we replaced with recursion helper function

```Rust
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

```

recursion extracts, but termination is not handled in Hax (we opened issue [#1882](https://github.com/cryspen/hax/issues/1882))

so we patch extracted file (add partial def for termination), patches are in file 
`scripts/extract_horner.sh`

**Can code preparation for extraction be automated?**

Yes, we can automate parts using codemods (automatic refactoring patterns) and extraction patches, but this depends on the maturity of the Hax-Lean backend; in the near term, a semi-automatic pipeline is realistic.

The steps we undertook in this pipeline can be automated:
- Replace for ... in slice.iter() with indexed while (or recursion) following a pattern
- Avoid dyn Trait → replace with function parameter/generic
- Replace Result/ensure → bool/Option for PoC
- Deterministic patch scripts (add import, replace def with partial def, etc.)

### What we are verifying (goal PoC)

we proved in file HornerLean/Proof.lean three simple useful PoC lemmas (but it is just shape/behavior) about extracted horner_eval_i64 (please check HornerLean/Proof.lean file)

to prove "mathematical" correctness 
(extracted horner_eval_i64 = evalAt (polyOfCoeffs ...))

we need: 

- panic freedom (no fail/div in RustM)
- prove no overflow у *? and +?
- bridge from i64 ↔ ℤ

(reminder: not real math correctness because of patches)

we prove next theorem (hornerZ is pure func over ℤ)
in file `lean/HornerLean/SpecProof.lean`

proved under temporary assumptions (axioms) due to missing simp/grind lemmas in CompPoly

`evalAt x (polyOfCoeffs cs) = hornerZ cs x`

## CompPoly gaps

CompPoly gaps (for full proof without assumptions)

1. @[simp]/@[grind] lemma:
   - CMvMonomial.toFinsupp (0 : CMvMonomial n) = 0
     (currently stuck on Vector.get 0 i = 0).
2. simp-friendly lemmas for Unlawful / Std.ExtTreeMap lookups used in proofs of         coefficient facts for C:
    - empty lookup (∅[m]? = none)
    - insert lookup ((t.insert k v)[k]? = some v, and ... = none for m ≠ k)
3. bridge lemmas:
    - fromCMvPolynomial (CMvPolynomial.C c) = MvPolynomial.C c
    - fromCMvPolynomial (CMvPolynomial.X i) = MvPolynomial.X i
4. finally:
        @[simp] eval_C
        @[simp] eval_X
5. We suggest to raise/run more pipelines from Plonky3, most likely we'll face more gaps:
    - More simp/grind lemma packs:
        - eval_pow, eval_sum, eval_monomial, lemmas about support, coeff
    - Univariate:
        - Lagrange interpolation (CompPoly/Univariate/Lagrange.lean) — add simp/automation lemmas
    - Multilinear:
        - multilinear extension evaluation (Multilinear/Basic.lean) — relates to zkVM
    - Normalization tactics:
        - curated simp set / grind set for polynomial goals


## Hax gaps (for complete end-to-end proof extracted → ℤ → CompPoly)

- was missing Core_models.Slice.Impl.is_empty (opened PR [#1885](https://github.com/cryspen/hax/pull/1885) and it was merged)
- recursion/termination (usize recursion) (issue [#1882](https://github.com/cryspen/hax/issues/1882)
- panic/overflow reasoning: +?/*? requires panic-freedom assumptions/lemmas
- semantic bridge i64 → ℤ under bounds

## Additional notes

**Lean spec: polynomial on ℤ in CompPoly and it's eval:**

- build polyOfCoeffs : List ℤ → CMvPolynomial 1 ℤ
- evalAt : ℤ → CMvPolynomial 1 ℤ → ℤ

**Proof plan (for PoC):**

- Proof: extracted Lean (hax) compiles + simple lemmas “shape/behavior” about extracted horner_eval_i64.
- Proof B (next layer): connect extracted i64‑calculations with mathematical ℤ‑spec considering, no overflow (precondition/bounds). This is “Rust → CompPoly” block of our pipeline.

to prove it we need next lemmas from CompPoly:

    evalAt x (C c) = c
    evalAt x X0 = x
    eval_add, eval_mul (already there)

    then we need to connect extracted RustM i64-Horner with hornerZ under bounds

    Then we will prove theorem:

    considering panic_free and no_overflow
    Horner_eval_rs.horner_eval_i64 coeffs x = ok r
      ⇒ (Int.ofInt64 r) = hornerZ (map Int.ofInt64 coeffs) (Int.ofInt64 x)

**file HornerLean/CompPolyAssumptions.lean**

While we were trying to prove eval_C and eval_X in CompPoly, we discovered missing "automation lemmas" (simp/grind-set gap). Example: in the current combination of Vector.get / Vector.replicate / simp-sets there's no available rewrite chain "replicate → get = constant".

So we created file HornerLean/CompPolyAssumptions.lean with temporary assumptions to unblock the PoC
