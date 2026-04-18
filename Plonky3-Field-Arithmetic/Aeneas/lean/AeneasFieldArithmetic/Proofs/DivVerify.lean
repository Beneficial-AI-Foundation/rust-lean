import Aeneas
import AeneasFieldArithmetic.Generated.Funs
import AeneasFieldArithmetic.Proofs.Interface
import AeneasFieldArithmetic.Proofs.MulVerify
import CompPoly.Fields.Mersenne

open Aeneas Aeneas.Std
open aeneas_field_arithmetic mersenne31.Mersenne31

variable (n m : m31)
variable (p q : Mersenne31.Field)

/--
Given two implementation `m31` elements such that
- Are valid Mersenne31 field elements
- The divisor is non-zero in the specification field

Projecting the extracted division into the specification field is the same
as projecting each element and performing the spec's division.

Division is defined as `a / b = a * b⁻¹` in both the implementation
and the specification (ZMod).
-/
theorem div_verify_to_spec
  (valid_n : UScalar.val n.value ≤ 2^31-1)
  (valid_m : UScalar.val m.value ≤ 2^31-1)
  (nonzero_m : to_m31_spec m valid_m ≠ 0) :
  to_m31_spec (divOk n m valid_n valid_m nonzero_m)
    (divOk_in_bounds n m valid_n valid_m nonzero_m) =
  to_m31_spec n valid_n / to_m31_spec m valid_m := by
  obtain ⟨inv, h_inv_ok, h_valid_inv, h_div_eq⟩ :=
    div_as_mul_inverse n m valid_m nonzero_m
  have h_inv_spec := inverse_to_spec m inv valid_m nonzero_m h_inv_ok
  simp only [divOk_eq_mul n m inv valid_n valid_m nonzero_m h_valid_inv h_div_eq]
  rw [mul_verify_to_spec n inv valid_n h_valid_inv, h_inv_spec, div_eq_mul_inv]

/--
Given two specification `Mersenne31.Field` elements such that the divisor is non-zero,
projecting the specification division into the implementation's field is the same as
projecting each element and performing the impl's division.
-/
theorem div_verify_of_spec
  (nonzero_q : q ≠ 0) :
  of_m31_spec (p / q) =
  divOk (of_m31_spec p) (of_m31_spec q)
    (Nat.le_of_lt (of_m31_spec_lt_m31 p))
    (Nat.le_of_lt (of_m31_spec_lt_m31 q))
    (by rwa [to_of_m31_eq]) := by
  rw [div_eq_mul_inv]
  have h_mul := mul_verify_of_spec p (q⁻¹)
  have h_valid_p := Nat.le_of_lt (of_m31_spec_lt_m31 p)
  have h_valid_q := Nat.le_of_lt (of_m31_spec_lt_m31 q)
  have h_nonzero_q : to_m31_spec (of_m31_spec q) h_valid_q ≠ 0 := by rwa [to_of_m31_eq]
  obtain ⟨inv, h_inv_ok, h_valid_inv, h_div_eq⟩ :=
    div_as_mul_inverse (of_m31_spec p) (of_m31_spec q) h_valid_q h_nonzero_q
  have h_inv_spec := inverse_to_spec (of_m31_spec q) inv h_valid_q h_nonzero_q h_inv_ok
  rw [to_of_m31_eq] at h_inv_spec
  have h_inv_lt : UScalar.val inv.value < 2^31-1 := by
    by_contra h_not_lt; push_neg at h_not_lt
    have : to_m31_spec inv h_valid_inv = 0 := by unfold to_m31_spec; rw [dif_neg (by omega)]
    rw [this] at h_inv_spec; exact absurd h_inv_spec.symm (inv_ne_zero nonzero_q)
  have h_eq_inv : of_m31_spec (q⁻¹) = inv :=
    to_m31_spec_inj _ inv (of_m31_spec_lt_m31 (q⁻¹)) h_inv_lt (by rw [to_of_m31_eq, h_inv_spec])
  rw [h_mul, h_eq_inv,
      divOk_eq_mul _ _ inv h_valid_p h_valid_q h_nonzero_q h_valid_inv h_div_eq]
