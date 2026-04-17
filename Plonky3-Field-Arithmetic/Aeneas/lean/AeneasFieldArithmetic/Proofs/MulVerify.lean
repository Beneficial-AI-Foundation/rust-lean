import Aeneas
import AeneasFieldArithmetic.Generated.Funs
import AeneasFieldArithmetic.Proofs.Interface
import CompPoly.Fields.Mersenne

open Aeneas Aeneas.Std

variable (n m : m31)
variable (p q : Mersenne31.Field)

/--
Given two implementation `m31` elements such that are valid
Mersenne31 field elements:
Projecting the extracted multiplication into the specification field is the same
as projecting each element and performing the spec's multiplication.
-/
theorem mul_verify_to_spec
  (valid_n : UScalar.val n.value ≤ 2^31-1)
  (valid_m : UScalar.val m.value ≤ 2^31-1) :
  to_m31_spec (mul_logic_nat n m)
    (mul_logic_nat_in_bounds n m) =
  to_m31_spec n valid_n * to_m31_spec m valid_m := by
  unfold to_m31_spec
  split <;> rename_i mlh
  · split
    · split
      · simp [mul_logic_nat, m31_of_u64_logic, U32.ofNatCore, UScalar.ofNatCore] at mlh
        split at mlh; contradiction
        simp_all
        simp [mul_logic_nat, m31_of_u64_logic, U32.ofNatCore, UScalar.ofNatCore]
        split <;> first | grind | congr
      · have : UScalar.val m.value = 2 ^ 31 - 1 := by grind
        simp [mul_logic_nat, m31_of_u64_logic, U32.ofNatCore, UScalar.ofNatCore] at mlh
        simp [mul_logic_nat, m31_of_u64_logic, U32.ofNatCore, UScalar.ofNatCore]
        simp_all
        split <;> split at mlh <;> try contradiction
        /- STRANGENESS NOTE: With (at least) Lean 4.28.0, having the
           following commented line results in a kernel error:
           `(kernel) deep recursion detected`
           To mitigate this, equivalent tactics are used inside the
           following `conv` block.  -/
        --simp only [UScalar.val, BitVec.toNat]
        conv=>
          lhs; congr
          -- Replaces the above `simp only`
          rw [UScalar.val, BitVec.toNat]; simp only
          rw [Nat.mod_eq_zero_of_dvd]
          · skip
          tactic=>
          -- Replaces the above `simp only`
            simp only [UScalar.val, BitVec.toNat]
            omega
        rfl
    · simp_all
      have : UScalar.val n.value = 2 ^ 31 - 1 := by grind
      simp [mul_logic_nat, m31_of_u64_logic, U32.ofNatCore, UScalar.ofNatCore] at mlh
      simp [mul_logic_nat, m31_of_u64_logic, U32.ofNatCore, UScalar.ofNatCore]
      simp_all
      split <;> split at mlh <;> try contradiction
      simp only [UScalar.val, BitVec.toNat]
      conv=>
        lhs; congr; rw [Nat.mod_eq_zero_of_dvd]
        · skip
        tactic=> omega
      rfl
  · simp_all
    have : ↑(mul_logic_nat n m).value = (2147483647 : ℕ) := by
      have := mul_logic_nat_in_bounds; grind
    simp [mul_logic_nat, m31_of_u64_logic, U32.ofNatCore, UScalar.ofNatCore] at this
    split at this <;> rename_i h <;> try cases h <;> simp_all
    · intro _ _; rename_i left _ _ _
      have := m31_mod_red; simp at this
      have left := congrArg (@Nat.cast Mersenne31.Field _) left
      conv at left=> lhs; rw [←this]
      simp at left; rw [←left]
      simp only [UScalar.val, BitVec.toNat]; congr
    · intro _ _; simp only [UScalar.val, BitVec.toNat] at this; lia

/-- The non-canonical zero representation `2^31-1` is unreachable in multiplication's
    modular reduction. -/
theorem mul_decomp_ne_noncanonical_zero :
    let prod := ZMod.val p * ZMod.val q
    let decomp := prod % 2147483648 + prod / 2147483648
    ¬(decomp % (2^31 - 1) = 0 ∧ decomp ≠ 0) := by
  simp only; intro ⟨h_mod, h_ne⟩; apply h_ne
  have hfs : Mersenne31.fieldSize = 2^31 - 1 := by unfold Mersenne31.fieldSize; ring
  have hp : ZMod.val p < 2^31 - 1 := hfs ▸ ZMod.val_lt p
  have hq : ZMod.val q < 2^31 - 1 := hfs ▸ ZMod.val_lt q
  have h_dvd : (2^31-1) ∣ (ZMod.val p * ZMod.val q) := by
    refine Nat.dvd_of_mod_eq_zero ?_
    have : ZMod.val p * ZMod.val q =
      (ZMod.val p * ZMod.val q % 2147483648 + ZMod.val p * ZMod.val q / 2147483648) +
      ZMod.val p * ZMod.val q / 2147483648 * (2^31 - 1) := by omega
    omega
  rcases fact_prime_2_31_sub_1.out.dvd_mul.mp h_dvd with ⟨c, hc⟩ | ⟨c, hc⟩
  · simp [show ZMod.val p = 0 from by omega]
  · simp [show ZMod.val q = 0 from by omega]

/--
Projecting the specification multiplication into the implementation's field is
the same as projecting each element and performing the impl's multiplication.
-/
theorem mul_verify_of_spec :
  of_m31_spec (p * q) =
  mul_logic_nat (of_m31_spec p) (of_m31_spec q)
  := by
  have special_case := mul_decomp_ne_noncanonical_zero p q
  have := m31_mod_red; simp at this
  have m31_rw : 2^31 - 1 = 2147483647 := rfl
  simp only [not_and_or] at special_case; cases special_case <;>
  simp [mul_logic_nat, m31_of_u64_logic]
  · rw [ite_cond_eq_false] <;> rw [m31_rw, ←this] at * <;>
    simp [val_of_m31_spec] <;> try grind
    congr
  · rw [ite_cond_eq_false] <;> try rw [m31_rw, ←this] at * <;>
    simp [val_of_m31_spec] <;> try grind
    congr
