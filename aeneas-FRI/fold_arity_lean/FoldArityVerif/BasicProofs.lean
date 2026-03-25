-- Basic correctness proofs for compute_log_arity_for_round (Aeneas extraction)
-- Preconditions mirror the original Plonky3 debug_assert! macros:
--   debug_assert!(log_current_height > log_final_height)
--   debug_assert!(log_current_height > next_log_height)  [when Some]
--
-- Compared to the Hax version:
--   • Aeneas extracts to a pure `Result` type (ok / fail / div) rather than
--     the monadic `RustM`.
--   • Scalar types are `Usize` (UScalar .Usize) with `.val : Nat` instead of
--     `usize` with `.toNat`.
--   • Standard Lean `Option` is used directly (not Core_models.Option.Option).
--   • Checked subtraction is built into the `Result` monad — no separate `-?`.

import Aeneas
import FoldArity

open Aeneas Aeneas.Std Result

namespace FoldArityVerif.BasicProofs

-- Helper: computation succeeds with value v
def returns {α : Type} (m : Result α) (v : α) : Prop :=
  m = ok v

-- Property 1: Result is always ≤ max_log_arity
-- (holds unconditionally for any successful call)
theorem bounded_by_max_log_arity
  (log_current_height : Usize)
  (next_input_log_height : Option Usize)
  (log_final_height : Usize)
  (max_log_arity : Usize)
  (result : Usize)
  (h_result : returns
    (fold_arity.compute_log_arity_for_round
      log_current_height next_input_log_height log_final_height max_log_arity)
    result)
  : result.val ≤ max_log_arity.val := by
  simp only [returns, fold_arity.compute_log_arity_for_round] at h_result
  -- Step 1: Name and case-split on first subtraction
  generalize h_sub1 : (log_current_height - log_final_height : Result Usize) = sub1 at h_result
  cases sub1 with
  | fail e | div  => simp at h_result
  | ok mft =>
    simp only [bind_tc_ok] at h_result
    -- Step 2: Case split on next_input_log_height
    cases next_input_log_height with
    | none =>
      simp only [] at h_result
      by_cases h_cmp : mft < max_log_arity
      · simp only [if_pos h_cmp, Result.ok.injEq] at h_result
        subst h_result; exact le_of_lt h_cmp
      · simp only [if_neg h_cmp, Result.ok.injEq] at h_result
        subst h_result; exact le_refl _
    | some nlh =>
      simp only [] at h_result
      generalize h_sub2 : (log_current_height - nlh : Result Usize) = sub2 at h_result
      cases sub2 with
      | fail e | div => simp at h_result
      | ok mfn =>
        simp only [bind_tc_ok] at h_result
        by_cases h_inner : mfn < mft
        · simp only [if_pos h_inner] at h_result
          by_cases h_outer : mfn < max_log_arity
          · simp only [if_pos h_outer, Result.ok.injEq] at h_result
            subst h_result; exact le_of_lt h_outer
          · simp only [if_neg h_outer, Result.ok.injEq] at h_result
            subst h_result; exact le_refl _
        · simp only [if_neg h_inner] at h_result
          by_cases h_outer : mft < max_log_arity
          · simp only [if_pos h_outer, Result.ok.injEq] at h_result
            subst h_result; exact le_of_lt h_outer
          · simp only [if_neg h_outer, Result.ok.injEq] at h_result
            subst h_result; exact le_refl _

-- Property 2: Result ≤ distance from current to final
-- (None case — no next-input constraint)
-- Requires the first debug_assert: log_current_height > log_final_height
theorem bounded_by_target_distance
  (log_current_height : Usize)
  (log_final_height : Usize)
  (max_log_arity : Usize)
  (result : Usize)
  (h_gt : log_current_height.val > log_final_height.val)
  (h_result : returns
    (fold_arity.compute_log_arity_for_round
      log_current_height none log_final_height max_log_arity)
    result)
  : result.val ≤ log_current_height.val - log_final_height.val := by
  unfold fold_arity.compute_log_arity_for_round at h_result
  simp [Bind.bind, Std.bind] at h_result
  have h_le : log_final_height.val ≤ log_current_height.val := by omega
  match h_sub : log_current_height - log_final_height with
  | .ok diff =>
    simp [h_sub, returns] at h_result
    split at h_result <;> {
      simp at h_result
      subst h_result
      have hsub := Std.Usize.sub_spec h_le
      simp [h_sub] at hsub
      omega
    }
  | .fail e | .div => simp [h_sub, returns] at h_result

-- Property 3: When next_input is Some, result ≤ distance from current to next
-- Requires both debug_asserts:
--   (a) log_current_height > log_final_height
--   (b) log_current_height > next_log_height
theorem respects_next_input
  (log_current_height : Usize)
  (next_log_height : Usize)
  (log_final_height : Usize)
  (max_log_arity : Usize)
  (result : Usize)
  (h_gt_final : log_current_height.val > log_final_height.val)
  (h_gt_next : log_current_height.val > next_log_height.val)
  (h_result : returns
    (fold_arity.compute_log_arity_for_round
      log_current_height
      (some next_log_height)
      log_final_height
      max_log_arity)
    result)
  : result.val ≤ log_current_height.val - next_log_height.val := by
  unfold fold_arity.compute_log_arity_for_round at h_result
  simp [Bind.bind, Std.bind] at h_result
  have h_le_final : log_final_height.val ≤ log_current_height.val := by omega
  have h_le_next : next_log_height.val ≤ log_current_height.val := by omega
  match h_sub1 : log_current_height - log_final_height with
  | .ok diff1 =>
    simp [h_sub1] at h_result
    match h_sub2 : log_current_height - next_log_height with
    | .ok diff2 =>
      simp [h_sub2, returns] at h_result
      have hsub2 := Std.Usize.sub_spec h_le_next
      simp [h_sub2] at hsub2
      split at h_result <;> split at h_result <;> {
        simp at h_result
        subst h_result
        omega
      }
    | .fail e | .div => simp [h_sub2, returns] at h_result
  | .fail e | .div => simp [h_sub1, returns] at h_result

-- Property 4: Result = min(distance constraints, max_log_arity)
-- Requires both debug_asserts
theorem takes_minimum_of_constraints
  (log_current_height : Usize)
  (next_log_height : Usize)
  (log_final_height : Usize)
  (max_log_arity : Usize)
  (result : Usize)
  (h_gt_final : log_current_height.val > log_final_height.val)
  (h_gt_next : log_current_height.val > next_log_height.val)
  (h_result : returns
    (fold_arity.compute_log_arity_for_round
      log_current_height
      (some next_log_height)
      log_final_height
      max_log_arity)
    result)
  : result.val ≤
      min (log_current_height.val - next_log_height.val) max_log_arity.val := by
  unfold fold_arity.compute_log_arity_for_round at h_result
  simp [Bind.bind, Std.bind] at h_result
  have h_le_final : log_final_height.val ≤ log_current_height.val := by omega
  have h_le_next : next_log_height.val ≤ log_current_height.val := by omega
  match h_sub1 : log_current_height - log_final_height with
  | .ok diff1 =>
    simp [h_sub1] at h_result
    match h_sub2 : log_current_height - next_log_height with
    | .ok diff2 =>
      simp [h_sub2, returns] at h_result
      have hsub2 := Std.Usize.sub_spec h_le_next
      simp [h_sub2] at hsub2
      split at h_result <;> split at h_result <;> {
        simp at h_result
        subst h_result
        obtain ⟨hsub2_eq, _⟩ := hsub2
        omega
      }
    | .fail e | .div => simp [h_sub2, returns] at h_result
  | .fail e | .div => simp [h_sub1, returns] at h_result

-- Property 5: None ≡ Some(log_final_height) — boundary case
-- When next-input IS the final height, the two cases coincide
theorem none_equals_some_at_target
  (log_current_height : Usize)
  (log_final_height : Usize)
  (max_log_arity : Usize)
  (result_none : Usize)
  (result_some : Usize)
  (h_gt : log_current_height.val > log_final_height.val)
  (h_none : returns
    (fold_arity.compute_log_arity_for_round
      log_current_height none log_final_height max_log_arity)
    result_none)
  (h_some : returns
    (fold_arity.compute_log_arity_for_round
      log_current_height
      (some log_final_height)
      log_final_height
      max_log_arity)
    result_some)
  : result_none = result_some := by
  unfold fold_arity.compute_log_arity_for_round at h_none h_some
  simp [Bind.bind, Std.bind] at h_none h_some
  have h_le : log_final_height.val ≤ log_current_height.val := by omega
  match h_sub : log_current_height - log_final_height with
  | .ok diff =>
    simp [h_sub, returns] at h_none h_some
    -- In h_some, the second subtraction is also log_current_height - log_final_height
    -- which is the same h_sub, so both reduce to the same if/else
    split at h_some <;> {
      rename_i h
      simp [h] at h_none
      simp at h_none h_some
      subst h_none
      subst h_some
      rfl
    }
  | .fail e | .div => simp [h_sub, returns] at h_none


-- Property 6: Monotone in max_log_arity
-- Larger cap ⟹ result can only be at least as large
theorem monotonic_in_max_arity
  (log_current_height : Usize)
  (next_input_log_height : Option Usize)
  (log_final_height : Usize)
  (max_log_arity1 max_log_arity2 : Usize)
  (result1 result2 : Usize)
  (h_gt : log_current_height.val > log_final_height.val)
  (h_le : max_log_arity1.val ≤ max_log_arity2.val)
  (h_result1 : returns
    (fold_arity.compute_log_arity_for_round
      log_current_height next_input_log_height log_final_height max_log_arity1)
    result1)
  (h_result2 : returns
    (fold_arity.compute_log_arity_for_round
      log_current_height next_input_log_height log_final_height max_log_arity2)
    result2)
  : result1.val ≤ result2.val := by
  unfold fold_arity.compute_log_arity_for_round at h_result1 h_result2
  simp [Bind.bind, Std.bind] at h_result1 h_result2
  have h_le_final : log_final_height.val ≤ log_current_height.val := by omega
  match h_sub1 : log_current_height - log_final_height with
  | .ok diff_final =>
    simp [h_sub1] at h_result1 h_result2
    cases next_input_log_height with
    | none =>
      simp [returns] at h_result1 h_result2
      -- Both results are min(diff_final, max_log_arity_i)
      split at h_result1 <;> split at h_result2 <;> {
        simp at h_result1 h_result2
        subst h_result1; subst h_result2
        omega
      }
    | some next_log =>
      simp at h_result1 h_result2
      match h_sub2 : log_current_height - next_log with
      | .ok diff_next =>
        simp [h_sub2, returns] at h_result1 h_result2
        -- 4 outer splits (diff_next < diff_final) × (diff < max_arity)
        -- but both h_result1 and h_result2 see the same diff_next/diff_final
        split at h_result1 <;> split at h_result1 <;>
          split at h_result2 <;> split at h_result2 <;> {
          simp at h_result1 h_result2
          subst h_result1; subst h_result2
          omega
        }
      | .fail e | .div => simp [h_sub2, returns] at h_result1
  | .fail e | .div => simp [h_sub1, returns] at h_result1

/-! ## Concrete examples -/

-- 10 - 3 = 7; max_arity 100 does not cap ⟹ result = 7
example :
  ∃ result,
    returns
      (fold_arity.compute_log_arity_for_round
        (Usize.ofNat 10) none (Usize.ofNat 3) (Usize.ofNat 100))
      result
    ∧ result.val = 7 := by
    exists (Usize.ofNat 7)
    constructor
    · unfold fold_arity.compute_log_arity_for_round returns
      simp [Bind.bind, Std.bind]
      unfold HSub.hSub instHSubUScalarResult
      simp
      unfold UScalar.sub
      simp
      split
      · simp [Std.Usize.ofNat, UScalar.ofNat]
        native_decide -- this works
      · simp_all; rename_i h; exact absurd h (by native_decide)
    · norm_num -- this works

-- 10 - 3 = 7; max_arity 4 caps ⟹ result = 4
example :
  ∃ result,
    returns
      (fold_arity.compute_log_arity_for_round
        (Usize.ofNat 10) none (Usize.ofNat 3) (Usize.ofNat 4))
      result
    ∧ result.val = 4 := by
    exists (Usize.ofNat 4)
    constructor
    · unfold fold_arity.compute_log_arity_for_round returns
      simp [Bind.bind, Std.bind]
      unfold HSub.hSub
      unfold instHSubUScalarResult
      simp
      unfold UScalar.sub
      simp
      native_decide
    · norm_num

-- next_input = 8: distance to next = 2, distance to final = 7 ⟹ result = 2
example :
  ∃ result,
    returns
      (fold_arity.compute_log_arity_for_round
        (Usize.ofNat 10) (some (Usize.ofNat 8)) (Usize.ofNat 3) (Usize.ofNat 100))
      result
    ∧ result.val = 2 := by
    exists (Usize.ofNat 2)
    unfold fold_arity.compute_log_arity_for_round returns
    simp [Bind.bind, Std.bind]
    unfold HSub.hSub
    unfold instHSubUScalarResult
    simp
    unfold UScalar.sub
    simp
    split
    · split
      · simp
        native_decide
      · simp_all; rename_i h; exact absurd h (by native_decide)
    · simp_all; rename_i h; exact absurd h (by native_decide)

end FoldArityVerif.BasicProofs
