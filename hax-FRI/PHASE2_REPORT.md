# Phase 2 Report — Implementation and Verification

## Introduction

This report summarises the work completed during Phase 2 of the project, whose objective was to
build a functional verification workflow and produce initial formal proofs for extracted
cryptographic Rust code.

During this phase we established two end-to-end pipelines that take Rust code through Hax
extraction into Lean 4 and produce machine-checked proofs. We verified key correctness properties
of the Plonky3 FRI folding kernel, contributed upstream improvements to the Hax toolchain, and
documented gaps in the Lean backend that inform future work.

---

## Our Contributions

### 1. Upstream Contributions to Hax

We merged two pull requests into the Hax repository:

| PR | Title | Description |
|----|-------|-------------|
| [#1927](https://github.com/cryspen/hax/pull/1927) | *lean: keep Rust crate/module names unchanged* | Fixed the Lean backend to preserve original Rust crate/module naming instead of capitalising the first letter, which caused Lake configuration friction. |
| [#1959](https://github.com/cryspen/hax/pull/1959) | *ADC example, documented* | Added a fully documented addition-with-carry (ADC) proof example demonstrating the `hax_mvcgen`, `specset "bv"`, and `hax_bv_decide` workflows. |

We also raised **6 issues** in the Hax repository, of which **4 have been closed as resolved**
(including our own fix in PR #1927):

| Issue | Title | Status |
|-------|-------|--------|
| [#1911](https://github.com/cryspen/hax/issues/1911) | Missing `Core_models.Ops.Arith.Add` instance for `+?` after `cast_op` | Closed (fixed in #1925) |
| [#1912](https://github.com/cryspen/hax/issues/1912) | `Add` instance missing for shift-left (`<<< ?`) with `i32` shift amount | Closed (fixed in #1925) |
| [#1913](https://github.com/cryspen/hax/issues/1913) | Extracted `Tuple2` lacks `.fst`/`.snd` projections | Closed |
| [#1914](https://github.com/cryspen/hax/issues/1914) | `cargo hax into lean` generates capitalised module names | Closed (fixed in #1927) |
| [#1915](https://github.com/cryspen/hax/issues/1915) | `hax_bv_decide` fails on extracted goals | Closed |
| [#1916](https://github.com/cryspen/hax/issues/1916) | Extraction emits monadic binds for pure arithmetic | Closed |

### 2. Pipeline Example: ADC Verification (Annotation-Based)

**Repository:** [runtimeverification/hax-annotations-adc-verification](https://github.com/runtimeverification/hax-annotations-adc-verification)

This pipeline demonstrates formal verification of a 32-bit addition-with-carry (ADC) function by
annotating Rust source code directly with Hax specifications. The verified properties include:

- No panics occur during execution.
- Carry values are constrained to {0, 1}.
- The arithmetic identity `a + b + carry = sum + 2^32 * carry_out` holds in 64-bit arithmetic.

This example also served as the primary vehicle for discovering and reporting the 6 Hax issues
listed above.

### 3. Pipeline Example: FRI Folding Verification (ArkLib Integration)

**Repository:** [runtimeverification/p3-hax-lean-fri-pipeline](https://github.com/runtimeverification/p3-hax-lean-fri-pipeline)

This pipeline extracts Plonky3's `compute_log_arity_for_round` function (a single FRI folding
step) from Rust into Lean 4 via Hax, and connects the extracted code to ArkLib's formal FRI
specifications.

**Proved theorems** (in `FoldingCorrectness.lean`):

- **`arity_respects_target_distance`** — The computed log-arity never exceeds the distance
  between the current domain height and the final height (`result ≤ log_current_height − log_final_height`).
  This ensures that a single folding round never overshoots the target domain size.

- **`arity_respects_max_bound`** — The computed log-arity is always bounded by
  `max_log_arity` (`result ≤ max_log_arity`), for both the `None` and `Some` branches
  of the next-input parameter. This holds unconditionally for any successful call.

Both proofs operate directly on the Hax-extracted monadic code (`RustM`), reasoning through
checked arithmetic (`-?`), constructor case-splits on `Core_models.Option`, and boolean
conditionals from `Machine_int.lt`.

### 4. Hax Lean Backend Gap Analysis

Through the proof work, we identified concrete gaps in Hax's Lean backend that make formal
verification harder than necessary. A detailed report with suggested fixes has been compiled in
[`HAX_MISSING_LEMMAS.md`](HAX_MISSING_LEMMAS.md). The key gaps are:

| Gap | Severity |
|-----|----------|
| No `@[simp]` discriminator lemmas for `RustM` constructors | High |
| No characterisation lemmas for checked arithmetic (`-?`, `+?`, `*?`) | High |
| Bool `if`-then-else vs. `ite` mismatch in generated code | High |
| No bridge lemma from `Machine_int.lt` to `Prop` | Medium |
| No `omega`/`norm_cast` integration for `USize64` | Medium |
| `Core_models.Option` constructor order reversed vs. stdlib | Low |

---

## Conclusion and Future Work

Phase 2 established two working Rust-to-Lean verification pipelines and produced the first
machine-checked proofs of FRI folding correctness properties against ArkLib specifications.
The upstream contributions (2 merged PRs, 6 issues) directly improved the Hax toolchain for
the broader community, and the gap analysis provides a concrete roadmap for making Hax's Lean
backend more proof-friendly.

In the next phase, we plan to build a similar proof-of-concept using
[Aeneas](https://github.com/AeneasVerif/aeneas) as an alternative Rust-to-Lean extraction
tool. This will allow a direct comparison of the two approaches — Hax (annotation-driven,
monadic extraction) vs. Aeneas (MIR-based, pure functional extraction) — in terms of
translation coverage, proof complexity, and tactic automation support. The goal is to determine
which pipeline is best suited for verifying real-world cryptographic code at scale.
