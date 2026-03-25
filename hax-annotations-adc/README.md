## PoC: Rust(with annotations) → Hax → Lean

Example in this repo: 32‑bit limb addition with carry (adc), a core operation in big‑integer and finite‑field arithmetic. Such low‑level primitives are essential for zero‑knowledge proof systems (e.g., Plonky3, Jolt, RISC‑Zero) 

The workflow follows the approach of [lean_barrett](https://github.com/cryspen/hax/tree/main/examples/lean_barrett) and [lean_chacha20](https://github.com/cryspen/hax/tree/main/examples/lean_chacha20): proofs are automatically extracted from Rust into Lean. Extracted code includes proofs already, done via annotations.

## function to verify: adc

`adc_u32(a,b,carry) -> (sum, carry_out)`

what we are adding as annotations (and theorem) to the rust code:

- carry ∈ {0,1}
- carry_out ∈ {0,1}
- mathematical correctness: a + b + carry = sum + 2^32 * carry_out (в u64)

This task can be solved using hax`s hax_bv_decide (bit blasting), like in [lean_barrett](https://github.com/cryspen/hax/tree/main/examples/lean_barrett) example.

in file src/lib.rs we have 
- rust code 
- specifications
- lean proof along with annotations


- adc_pre/adc_post — separate functions, like in barrett example: this simplifies unfolding in Lean.
- We add theorem through #[hax_lib::lean::after("...")], so it appears directly in extracted .lean.
- proof is automatic via hax_bv_decide.

## what we prove:


- function wouldn't panic
- function result would satisfy mathematical spec for ADC

mathematical specification for ADC:

```rust
lhs = a as u64 + b as u64 + carry as u64
rhs = sum as u64 + (carry_out as u64) << 32
lhs == rhs
```

## problems (hax issues we identify and open + PRs)

After running `cargo hax into lean`, extracted lean file wouldn't compile because of next gaps:

- Adding u64 + u64 after casts from u32 (missing Core_models.Ops.Arith.Add instance for +? after cast_op (type inference)). Issue #[1911](https://github.com/cryspen/hax/issues/1911)
- Addition with a bit shift result (Issue with casts between types of different bit widths) Issue #[1912] (https://github.com/cryspen/hax/issues/1912)
- Extraction emits monadic binds for pure arithmetic, so type inference and automation gets harder
Issue #[1916] (https://github.com/cryspen/hax/issues/1916) Closed, discussed.
- Tuple2 does not provide .fst/.snd access methods (Missing projection functions for tuples)
[PR fixing issue](https://github.com/cryspen/hax/pull/1917), closed due to discussion in issue [#1913](https://github.com/cryspen/hax/issues/1913)
- error with hax_bv_decide ("None of the hypotheses are in the supported BitVec fragment") which means that tactic can not work with current operations representation
Issue #[1915] (https://github.com/cryspen/hax/issues/1915) Closed as duplication of [#1894](https://github.com/cryspen/hax/issues/1894)
- Mismatch between Rust and Lean naming conventions (Hax_adc_poc vs hax_adc_poc - had to rename manually or fix lakefile.toml after extraction) Issue #[1914] (https://github.com/cryspen/hax/issues/1914). [PR fixing issue](https://github.com/cryspen/hax/pull/1927)

