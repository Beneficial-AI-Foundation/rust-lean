-- Correctness proofs for fold_step (Aeneas extraction of arity-2 FRI folding)
--
-- The Rust function fold_step computes the core FRI folding operation:
--   fold_step(lo, hi, β, x⁻¹, 2⁻¹, p) = ((lo + hi) + β · (lo − hi) · x⁻¹) · 2⁻¹  mod p
--
-- This is the evaluation of foldNth(2, f, β) at x², where lo = f(x), hi = f(−x).
--
-- Compared to fold_arity (scheduling logic), this function performs actual
-- field arithmetic — the core of every FRI round.

import Aeneas
import FoldStep

open Aeneas Aeneas.Std Result

namespace FoldStepVerif.BasicProofs

/-! ## Pure Nat specification -/

/-- The mathematical specification of fold_step as a Nat computation.
    This mirrors the Rust implementation step-by-step over natural numbers. -/
def fold_step_nat (lo hi beta x_inv two_inv p : Nat) : Nat :=
  let sum := (lo + hi) % p
  let diff := (lo + p - hi) % p
  let t := (diff * x_inv) % p
  let bt := (beta * t) % p
  let combined := (sum + bt) % p
  (combined * two_inv) % p

/-- fold_step_nat always produces a result < p (when p > 0) -/
theorem fold_step_nat_bounded {lo hi beta x_inv two_inv p : Nat} (hp : 0 < p) :
    fold_step_nat lo hi beta x_inv two_inv p < p := by
  unfold fold_step_nat
  exact Nat.mod_lt _ hp

/-! ## Safe-parameter predicate -/

/-- Preconditions ensuring fold_step cannot overflow.
    All inputs are field elements (< p), and p is small enough that
    intermediate products fit in u64. -/
structure SafeFieldParams (lo hi beta x_inv two_inv p : U64) : Prop where
  hp_pos : p.val ≠ 0
  hlo : lo.val < p.val
  hhi : hi.val < p.val
  hbeta : beta.val < p.val
  hx_inv : x_inv.val < p.val
  htwo_inv : two_inv.val < p.val
  -- p² fits in u64 (ensures multiplications don't overflow)
  hp_mul : p.val * p.val ≤ U64.max
  -- 2p fits in u64 (ensures additions don't overflow)
  hp_add : p.val + p.val ≤ U64.max + 1

/-! ## Main specification theorem -/

/-- fold_step succeeds under safe parameters and computes fold_step_nat.
    This is the key theorem: the Rust implementation matches the pure specification. -/
theorem fold_step_spec
    (lo hi beta x_inv two_inv p : U64)
    (safe : SafeFieldParams lo hi beta x_inv two_inv p) :
    fold_step.fold_step lo hi beta x_inv two_inv p ⦃ result =>
      result.val = fold_step_nat lo.val hi.val beta.val x_inv.val two_inv.val p.val ∧
      result.val < p.val ⦄ := by
  obtain ⟨hp, hlo, hhi, hbeta, hx_inv, htwo_inv, hp_mul, hp_add⟩ := safe
  unfold fold_step.fold_step
  -- Step 1: lo + hi (addition, both < p, so sum < 2p ≤ U64.max + 1)
  progress as ⟨i, hi_eq⟩
  -- Step 2: i % p
  progress as ⟨sum, hsum⟩
  have hsum_lt : sum.val < p.val := by
    rw [show sum.val = i.val % p.val from hsum]
    exact Nat.mod_lt _ (by omega)
  -- Step 3: lo + p (< 2p ≤ U64.max + 1)
  progress as ⟨i1, hi1⟩
  -- Step 4: i1 - hi (i1 = lo + p ≥ p > hi)
  progress as ⟨i2, hi2, _⟩
  -- Step 5: i2 % p
  progress as ⟨diff, hdiff⟩
  have hdiff_lt : diff.val < p.val := by
    rw [show diff.val = i2.val % p.val from hdiff]
    exact Nat.mod_lt _ (by omega)
  -- Step 6: diff * x_inv (both < p, so product < p² ≤ U64.max)
  progress as ⟨i3, hi3⟩
  · -- Nonlinear bound: diff < p, x_inv < p, so diff * x_inv ≤ p * p ≤ U64.max
    have : diff.val ≤ p.val := by omega
    have : x_inv.val ≤ p.val := by omega
    nlinarith
  -- Step 7: i3 % p
  progress as ⟨t, ht⟩
  have ht_lt : t.val < p.val := by
    rw [show t.val = i3.val % p.val from ht]
    exact Nat.mod_lt _ (by omega)
  -- Step 8: beta * t (both < p, product < p² ≤ U64.max)
  progress as ⟨i4, hi4⟩
  · have : beta.val ≤ p.val := by omega
    have : t.val ≤ p.val := by omega
    nlinarith
  -- Step 9: i4 % p
  progress as ⟨bt, hbt⟩
  have hbt_lt : bt.val < p.val := by
    rw [show bt.val = i4.val % p.val from hbt]
    exact Nat.mod_lt _ (by omega)
  -- Step 10: sum + bt (both < p, sum < 2p ≤ U64.max + 1)
  progress as ⟨i5, hi5⟩
  -- Step 11: i5 % p
  progress as ⟨i6, hi6⟩
  have hi6_lt : i6.val < p.val := by
    rw [show i6.val = i5.val % p.val from hi6]
    exact Nat.mod_lt _ (by omega)
  -- Step 12: i6 * two_inv (both < p, product < p² ≤ U64.max)
  progress as ⟨i7, hi7⟩
  · have : i6.val ≤ p.val := by omega
    have : two_inv.val ≤ p.val := by omega
    nlinarith
  -- Step 13: i7 % p (final result)
  progress as ⟨result, hresult⟩
  have hresult_lt : result.val < p.val := by
    rw [show result.val = i7.val % p.val from hresult]
    exact Nat.mod_lt _ (by omega)
  -- Close: result matches fold_step_nat and is bounded
  constructor
  · -- Specification equality: chain all intermediate equalities
    unfold fold_step_nat
    simp_all
  · exact hresult_lt

/-! ## Corollary: fold_step always succeeds under safe parameters -/

theorem fold_step_succeeds
    (lo hi beta x_inv two_inv p : U64)
    (safe : SafeFieldParams lo hi beta x_inv two_inv p) :
    ∃ result, fold_step.fold_step lo hi beta x_inv two_inv p = ok result := by
  have h := fold_step_spec lo hi beta x_inv two_inv p safe
  simp only [WP.spec] at h
  match heq : fold_step.fold_step lo hi beta x_inv two_inv p with
  | ok r => exact ⟨r, rfl⟩
  | fail _ => simp [heq, WP.theta] at h
  | div => simp [heq, WP.theta] at h

/-! ## Concrete examples -/

-- Example: p = 7 (small prime), lo = 3 = f(x), hi = 5 = f(-x), beta = 2, x_inv = 4 (= x⁻¹), two_inv = 4 (= 2⁻¹ mod 7)
-- fold_step_nat 3 5 2 4 4 7
--   sum   = (3 + 5) % 7 = 1
--   diff  = (3 + 7 - 5) % 7 = 5
--   t     = (5 * 4) % 7 = 6
--   bt    = (2 * 6) % 7 = 5
--   comb  = (1 + 5) % 7 = 6
--   result = (6 * 4) % 7 = 3
example : fold_step_nat 3 5 2 4 4 7 = 3 := by native_decide

-- Verify the Rust function matches on the same inputs
example :
    fold_step.fold_step
      (U64.ofNat 3) (U64.ofNat 5) (U64.ofNat 2)
      (U64.ofNat 4) (U64.ofNat 4) (U64.ofNat 7)
    = ok (U64.ofNat 3) := by rfl

-- Example: p = 17, lo = 10, hi = 7, beta = 3, x_inv = 2 (x=9, 9*2=18≡1), two_inv = 9 (2*9=18≡1)
-- fold_step_nat 10 7 3 2 9 17
--   sum   = (10 + 7) % 17 = 0
--   diff  = (10 + 17 - 7) % 17 = 3
--   t     = (3 * 2) % 17 = 6
--   bt    = (3 * 6) % 17 = 1
--   comb  = (0 + 1) % 17 = 1
--   result = (1 * 9) % 17 = 9
example : fold_step_nat 10 7 3 2 9 17 = 9 := by native_decide

example :
    fold_step.fold_step
      (U64.ofNat 10) (U64.ofNat 7) (U64.ofNat 3)
      (U64.ofNat 2) (U64.ofNat 9) (U64.ofNat 17)
    = ok (U64.ofNat 9) := by rfl

end FoldStepVerif.BasicProofs
