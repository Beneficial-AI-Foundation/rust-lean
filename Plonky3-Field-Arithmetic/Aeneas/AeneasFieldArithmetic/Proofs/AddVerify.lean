import Aeneas
import AeneasFieldArithmetic.Generated.Funs
import AeneasFieldArithmetic.Proofs.Interface
import CompPoly.Fields.Mersenne

open Aeneas Aeneas.Std

variable (n m : m31)
variable (p q : Mersenne31.Field)

/--
Given two implementation `m31` elements such that
- Are valid Mersenne31 field elements
- Their casted natural addition wont be exactly the Mersenne prime

Projecting the extracted addition into the specification field is the same
as projecting each element and performing the spec's addition.
-/
theorem add_verify_to_spec
  (valid_n : UScalar.val n.value ≤ 2^31-1)
  (valid_m : UScalar.val m.value ≤ 2^31-1) :
  to_m31_spec ⟨add_logic n m valid_n valid_m⟩
    (add_logic_in_bounds n m valid_n valid_m) =
  to_m31_spec n valid_n + to_m31_spec m valid_m := by
  unfold to_m31_spec; split
  · split <;>
      split <;>
      simp [add_logic] <;> simp only [UScalar.val] <;>
      congr <;> simp <;> split <;> rename_i h _ _ _ <;>
      rw [add_logic] at h <;> grind
  · split
    · split <;> rename_i h _ _  <;> simp [add_logic] at h
      · split at h <;> rename_i h2
        · simp only [UScalar.ofNatCore, UScalar.val] at h
          unfold UScalar.val at h; simp at h
          have sum_eq : ↑n.value + ↑m.value = (2147483647 : ℕ) := by grind
          refine Arith.ZMod_val_injective ?_
          simp [ZMod.val_add]; simp only [ZMod.val, sum_eq]
          grind
        -- TODO: Merge these two proofs
        · simp only [UScalar.ofNatCore, UScalar.val] at h
          unfold UScalar.val at h; simp at h
          have sum_eq : ↑n.value + ↑m.value = (2147483647 : ℕ) := by grind
          refine Arith.ZMod_val_injective ?_
          simp [ZMod.val_add]; simp only [ZMod.val, sum_eq]
          grind
      · split at h <;> rename_i h2 <;>
        simp only [UScalar.ofNatCore, UScalar.val] at h <;>
        unfold UScalar.val at h; simp at h
        -- TODO: Collapse these two subproofs into one
        · have sum_eq : ↑n.value + ↑m.value = (2147483647 : ℕ) := by grind
          have m_eq : ↑m.value = (2147483647 : ℕ) := by grind
          have n_eq : ↑n.value = (0 : ℕ) := by grind
          refine Arith.ZMod_val_injective ?_
          simp [n_eq]
        · have m_eq : ↑m.value = (2147483647 : ℕ) := by grind
          have n_eq : ↑n.value = (0 : ℕ) := by grind
          refine Arith.ZMod_val_injective ?_
          simp [n_eq]
    · split <;> rename_i h _ _  <;> simp [add_logic] at h <;>
      split at h <;> rename_i h2 <;> try simp <;> simp at h2 <;>
      simp only [UScalar.ofNatCore, UScalar.val] at h <;>
      simp only [BitVec.toNat] at h <;> simp at h
      · have n_eq : ↑n.value = (2147483647 : ℕ) := by grind
        have m_eq : ↑m.value = (0 : ℕ) := by grind
        refine Arith.ZMod_val_injective ?_
        simp [m_eq]
      -- TODO: Collapse these two subproofs into one
      · have n_eq : ↑n.value = (2147483647 : ℕ) := by grind
        have m_eq : ↑m.value = (0 : ℕ) := by grind
        refine Arith.ZMod_val_injective ?_
        simp [m_eq]

/--
Given two specification `Mersenne31.Field` elements such that
- Their casted natural addition wont be exactly the Mersenne prime

Projecting the specification addition into the implementation's field is
the same as projecting each element and performing the impl's addition.
-/
theorem add_verify_of_spec
  (special_case : (ZMod.val p) + (ZMod.val q) ≠ 2^31 - 1) :
  of_m31_spec (p + q) =
  ⟨add_logic (of_m31_spec p) (of_m31_spec q) (Nat.le_of_lt (of_m31_spec_lt_m31 p)) ((Nat.le_of_lt (of_m31_spec_lt_m31 q)))⟩
  := by
  simp [add_logic, of_m31_spec]; split <;> rename_i h <;>
  simp [U32.ofNatCore, UScalar.ofNatCore] <;> try simp at h
  · simp [Nat.le_iff_lt_or_eq] at h; cases h
    · rw [ZMod.val_add_of_lt]; assumption
    · contradiction
  · rw [ZMod.val_add_of_le (Nat.le_of_lt h)]
