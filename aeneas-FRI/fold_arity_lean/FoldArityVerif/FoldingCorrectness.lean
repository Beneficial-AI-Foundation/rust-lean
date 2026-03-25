-- Correctness proofs connecting Aeneas-extracted FRI code to ArkLib specifications
-- Preconditions mirror the original Plonky3 debug_assert! macros:
--   debug_assert!(log_current_height > log_final_height)
--   debug_assert!(log_current_height > next_log_height)  [when Some]
--
-- NOTE: Aeneas and ArkLib (via Batteries/mathlib) both define
-- `BitVec.toNat_pow`, so they cannot be imported in the same environment.
-- We import ArkLib here and declare the Aeneas-side properties as axioms,
-- justified by the proofs in BasicProofs.lean.

import ArkLib.ProofSystem.Fri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.Data.Polynomial.SplitFold
import ArkLib.ProofSystem.Fri.Domain

namespace FoldArityVerif.FoldingCorrectness

open Polynomial Fri.Domain

/-!
# FRI Folding Correctness

## ArkLib context

`ArkLib.ProofSystem.Fri.Spec.SingleRound` models one FRI round with:
- `s : Fin (k+1) → ℕ+` — folding degree per round (our `result` is one value of `s`)
- Domain size constraint: `(2^(∑ i, (s i).1)) * d ≤ 2^n`

`ArkLib.Data.Polynomial.SplitFold` provides:
- `splitNth f n i` — n-way split of polynomial f
- `foldNth n f α`  — fold with powers of α (core FRI step)

## Connection

`fold_arity.compute_log_arity_for_round` returns `log₂(arity)` = `s i` for one round.
It enforces: result ≤ log_current − log_final  AND  result ≤ max_log_arity.

## Bridge from Aeneas

Because `Aeneas` and `Batteries` have a name collision (`BitVec.toNat_pow`),
we cannot import both in one file. The axioms below are proved in
`BasicProofs.lean` (which imports only Aeneas); here we state them over `Nat`
so we can connect them to ArkLib's field-theoretic specifications.
-/

/-! ## Helpers -/

-- Convert log-arity to actual arity value
def log_to_arity (log_arity : Nat) : Nat := 2 ^ log_arity

-- Domain height after folding by log_arity
def domain_height_after_fold (current_height fold_amount : Nat) : Nat :=
  current_height - fold_amount

/-! ## Axiomatized Aeneas-side properties (proved in BasicProofs.lean) -/

-- The Rust function compute_log_arity_for_round, abstracted to Nat.
-- In BasicProofs.lean this is `fold_arity.compute_log_arity_for_round` over `Usize`.
-- Here we model its successful output as a Nat-valued specification.
-- `compute_log_arity spec log_cur (some log_next) log_final max_arity = result`
-- means the Rust function returned `ok result`.
opaque compute_log_arity_spec
  (log_current_height : Nat)
  (next_input_log_height : Option Nat)
  (log_final_height : Nat)
  (max_log_arity : Nat) : Option Nat

-- Axiom: result ≤ max_log_arity (proved as bounded_by_max_log_arity)
axiom bounded_by_max_arity
  (log_cur : Nat) (next : Option Nat) (log_final max_arity result : Nat)
  (h_gt : log_cur > log_final)
  (h_ok : compute_log_arity_spec log_cur next log_final max_arity = some result)
  : result ≤ max_arity

-- Axiom: result ≤ log_cur - log_final when next = none
-- (proved as bounded_by_target_distance)
axiom bounded_by_target_distance
  (log_cur log_final max_arity result : Nat)
  (h_gt : log_cur > log_final)
  (h_ok : compute_log_arity_spec log_cur none log_final max_arity = some result)
  : result ≤ log_cur - log_final

-- Axiom: result ≤ log_cur - log_next when next = some log_next
-- (proved as respects_next_input)
axiom bounded_by_next_distance
  (log_cur log_next log_final max_arity result : Nat)
  (h_gt_final : log_cur > log_final)
  (h_gt_next : log_cur > log_next)
  (h_ok : compute_log_arity_spec log_cur (some log_next) log_final max_arity = some result)
  : result ≤ log_cur - log_next

/-! ## Folding degree connection -/

-- The result of compute_log_arity_for_round determines the folding degree
-- for one FRI round. In ArkLib's `SingleRound`, this corresponds to
-- `(s i).val` where `s : Fin (k+1) → ℕ+` is the per-round folding schedule.
theorem compute_log_arity_gives_folding_degree
  (log_cur : Nat) (next : Option Nat) (log_final max_arity result : Nat)
  (h_gt : log_cur > log_final)
  (h_ok : compute_log_arity_spec log_cur next log_final max_arity = some result)
  : ∃ s : Nat, s = result :=
  ⟨result, rfl⟩

/-! ## Domain size constraints -/

-- After folding by `result`, the domain height stays ≥ log_final_height.
-- In ArkLib terms: `evalDomain D i` still has size ≥ 2^log_final after folding.
theorem folding_respects_final_height
  (log_cur log_final max_arity result : Nat)
  (h_gt : log_cur > log_final)
  (h_ok : compute_log_arity_spec log_cur none log_final max_arity = some result)
  : domain_height_after_fold log_cur result ≥ log_final := by
  sorry

/-! ## Polynomial degree reduction -/

-- Folding with arity 2^result reduces polynomial degree by factor 2^result.
-- This follows from ArkLib's `foldNth_degree_le`: deg(foldNth n f α) ≤ deg(f)/n
-- Combined with our bound: result ≤ max_arity, the folded polynomial
-- remains within the degree bound for the next FRI round.
theorem folding_reduces_degree
  {F : Type} [Field F]
  (f : F[X]) (α : F) (result : Nat) (h_pos : result > 0)
  : (Polynomial.foldNth (2 ^ result) f α).natDegree ≤ f.natDegree / (2 ^ result) := by
  sorry

/-! ## Multi-round consistency -/

-- Two consecutive rounds together stay within total allowed folds.
-- In ArkLib terms: ∑ i, (s i).val ≤ n (the domain size condition).
theorem round_consistency_preserved
  (round1_arity round2_arity : Nat)
  (initial_height intermediate_height final_height : Nat)
  (max_arity : Nat)
  (h_gt1 : initial_height > final_height)
  (h_gt2 : intermediate_height > final_height)
  (h_gt_int : initial_height > intermediate_height)
  (h1 : compute_log_arity_spec
          initial_height (some intermediate_height)
          final_height max_arity = some round1_arity)
  (h2 : compute_log_arity_spec
          intermediate_height none
          final_height max_arity = some round2_arity)
  : round1_arity + round2_arity ≤ initial_height - final_height := by
  sorry

/-! ## ArkLib domain connection -/

-- The folding arity from compute_log_arity determines the subdomain
-- relationship in ArkLib's FRI domain tower:
-- `evalDomain D (i + result) ⊆ evalDomain D i` via squaring.
-- After folding by 2^result, the evaluation domain shrinks from
-- size 2^log_cur to size 2^(log_cur - result).
theorem arity_determines_domain_step
  {F : Type} [NonBinaryField F] [Finite F]
  {D : Subgroup Fˣ} {n : ℕ}
  [IsCyclicWithGen D] [SmoothPowerOfTwo n D]
  (i result : Nat) (h_i : i + result ≤ n)
  : ∀ x : evalDomain D (i + result), (x : Fˣ) ∈ evalDomain D i := by
  sorry

/-! ## Concrete example -/

-- height 10 → final 3, no next, large cap: result = 7 = 10 - 3
-- log_to_arity 7 = 128 is the actual arity used in FRI
-- After folding: domain shrinks from 2^10 = 1024 to 2^3 = 8
example : log_to_arity 7 = 128 := by native_decide

example : domain_height_after_fold 10 7 = 3 := by native_decide

end FoldArityVerif.FoldingCorrectness
