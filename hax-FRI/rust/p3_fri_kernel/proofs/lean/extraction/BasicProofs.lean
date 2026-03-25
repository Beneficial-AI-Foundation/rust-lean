-- Basic correctness proofs for compute_log_arity_for_round
-- Preconditions mirror the original Plonky3 debug_assert! macros:
--   debug_assert!(log_current_height > log_final_height)
--   debug_assert!(log_current_height > next_log_height)  [when Some]

import Hax
import CoreModelsPatch
import «p3_fri_kernel»

open Std.Do
open Std.Tactic

namespace P3FriKernel.BasicProofs

-- Helper: computation succeeds with value v
def returns (m : RustM α) (v : α) : Prop :=
  m = pure v

-- Property 1: Result is always ≤ max_log_arity
-- (holds unconditionally for any successful call)
theorem bounded_by_max_log_arity
  (log_current_height : usize)
  (next_input_log_height : Core_models.Option.Option usize)
  (log_final_height : usize)
  (max_log_arity : usize)
  (result : usize)
  (h_gt   : log_current_height.toNat > log_final_height.toNat)
  (h_result : returns
    (P3_fri_kernel.compute_log_arity_for_round
      log_current_height next_input_log_height log_final_height max_log_arity)
    result)
  : result.toNat ≤ max_log_arity.toNat := by
  sorry

-- Property 2: Result ≤ distance from current to final
-- (None case — no next-input constraint)
-- Requires the first debug_assert: log_current_height > log_final_height
theorem bounded_by_target_distance
  (log_current_height : usize)
  (log_final_height : usize)
  (max_log_arity : usize)
  (result : usize)
  (h_gt : log_current_height.toNat > log_final_height.toNat)
  (h_result : returns
    (P3_fri_kernel.compute_log_arity_for_round
      log_current_height Core_models.Option.Option.None log_final_height max_log_arity)
    result)
  : result.toNat ≤ log_current_height.toNat - log_final_height.toNat := by
  sorry

-- Property 3: When next_input is Some, result ≤ distance from current to next
-- Requires both debug_asserts:
--   (a) log_current_height > log_final_height
--   (b) log_current_height > next_log_height
theorem respects_next_input
  (log_current_height : usize)
  (next_log_height : usize)
  (log_final_height : usize)
  (max_log_arity : usize)
  (result : usize)
  (h_gt_final : log_current_height.toNat > log_final_height.toNat)
  (h_gt_next  : log_current_height.toNat > next_log_height.toNat)
  (h_result : returns
    (P3_fri_kernel.compute_log_arity_for_round
      log_current_height
      (Core_models.Option.Option.Some next_log_height)
      log_final_height
      max_log_arity)
    result)
  : result.toNat ≤ log_current_height.toNat - next_log_height.toNat := by
  sorry

-- Property 4: Result = min(distance constraints, max_log_arity)
-- Requires both debug_asserts
theorem takes_minimum_of_constraints
  (log_current_height : usize)
  (next_log_height : usize)
  (log_final_height : usize)
  (max_log_arity : usize)
  (result : usize)
  (h_gt_final : log_current_height.toNat > log_final_height.toNat)
  (h_gt_next  : log_current_height.toNat > next_log_height.toNat)
  (h_result : returns
    (P3_fri_kernel.compute_log_arity_for_round
      log_current_height
      (Core_models.Option.Option.Some next_log_height)
      log_final_height
      max_log_arity)
    result)
  : result.toNat ≤
      min (log_current_height.toNat - next_log_height.toNat) max_log_arity.toNat := by
  sorry

-- Property 5: None ≡ Some(log_final_height) — boundary case
-- When next-input IS the final height, the two cases coincide
theorem none_equals_some_at_target
  (log_current_height : usize)
  (log_final_height : usize)
  (max_log_arity : usize)
  (result_none : usize)
  (result_some : usize)
  (h_gt : log_current_height.toNat > log_final_height.toNat)
  (h_none : returns
    (P3_fri_kernel.compute_log_arity_for_round
      log_current_height Core_models.Option.Option.None log_final_height max_log_arity)
    result_none)
  (h_some : returns
    (P3_fri_kernel.compute_log_arity_for_round
      log_current_height
      (Core_models.Option.Option.Some log_final_height)
      log_final_height
      max_log_arity)
    result_some)
  : result_none = result_some := by
  sorry

-- Property 6: Monotone in max_log_arity
-- Larger cap ⟹ result can only be at least as large
theorem monotonic_in_max_arity
  (log_current_height : usize)
  (next_input_log_height : Core_models.Option.Option usize)
  (log_final_height : usize)
  (max_log_arity1 max_log_arity2 : usize)
  (result1 result2 : usize)
  (h_gt : log_current_height.toNat > log_final_height.toNat)
  (h_le : max_log_arity1.toNat ≤ max_log_arity2.toNat)
  (h_result1 : returns
    (P3_fri_kernel.compute_log_arity_for_round
      log_current_height next_input_log_height log_final_height max_log_arity1)
    result1)
  (h_result2 : returns
    (P3_fri_kernel.compute_log_arity_for_round
      log_current_height next_input_log_height log_final_height max_log_arity2)
    result2)
  : result1.toNat ≤ result2.toNat := by
  sorry

/-! ## Concrete examples -/

-- 10 - 3 = 7; max_arity 100 does not cap ⟹ result = 7
example :
  ∃ result,
    returns
      (P3_fri_kernel.compute_log_arity_for_round ⟨10⟩ Core_models.Option.Option.None ⟨3⟩ ⟨100⟩)
      result
    ∧ result.toNat = 7 := by
  sorry

-- 10 - 3 = 7; max_arity 4 caps ⟹ result = 4
example :
  ∃ result,
    returns
      (P3_fri_kernel.compute_log_arity_for_round ⟨10⟩ Core_models.Option.Option.None ⟨3⟩ ⟨4⟩)
      result
    ∧ result.toNat = 4 := by
  sorry

-- next_input = 8: distance to next = 2, distance to final = 7 ⟹ result = 2
example :
  ∃ result,
    returns
      (P3_fri_kernel.compute_log_arity_for_round
        ⟨10⟩ (Core_models.Option.Option.Some ⟨8⟩) ⟨3⟩ ⟨100⟩)
      result
    ∧ result.toNat = 2 := by
  sorry

end P3FriKernel.BasicProofs
