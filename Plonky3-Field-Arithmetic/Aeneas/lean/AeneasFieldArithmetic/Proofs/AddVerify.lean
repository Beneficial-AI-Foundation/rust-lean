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
  (valid_n : UScalar.val n.value < 2^31-1)
  (valid_m : UScalar.val m.value < 2^31-1)
  (special_case : UScalar.val n.value + ↑m.value ≠ (2^31-1 : ℕ)) :
  to_m31_spec (addOk n m valid_n valid_m)
    (addOk_in_bounds n m valid_n valid_m special_case) =
  to_m31_spec n valid_n + to_m31_spec m valid_m := by
  unfold addOk to_m31_spec UScalar.val; congr; split <;> rename_i h <;> rw [add_spec] at h
  any_goals assumption
  any_goals contradiction
  simp at h; rw [←h]; simp [add_logic]; split; grind
  rename_i h2; simp at h2
  simp only [UScalar.ofNatCore, UScalar.val, BitVec.toNat]; grind

/--
Given two specification `Mersenne31.Field` elements such that
- Their casted natural addition wont be exactly the Mersenne prime

Projecting the specification addition into the implementation's field is
the same as projecting each element and performing the impl's addition.
-/
theorem add_verify_of_spec
  (special_case : (ZMod.val p) + (ZMod.val q) ≠ 2^31 - 1) :
  of_m31_spec (p + q) =
  addOk (of_m31_spec p) (of_m31_spec q) (of_m31_spec_lt_m31 p) (of_m31_spec_lt_m31 q)
  := by
  simp [addOk, of_m31_spec]; split <;> rename_i h <;> rw [add_spec] at h <;> try simp <;> try grind
  any_goals contradiction
  simp at h; rw [←h]; simp [add_logic, ZMod.val_add, Mersenne31.fieldSize]; split; grind
  simp only [ZMod.val] at *
  rename_i h2; simp at h2; simp [U32.ofNatCore, UScalar.ofNatCore]
  rw [Nat.mod_eq]
  split; grind
  rename_i fls; simp at fls; simp [ZMod.val] at h2; omega
