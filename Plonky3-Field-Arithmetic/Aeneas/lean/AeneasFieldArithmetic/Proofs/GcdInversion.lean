import Aeneas
import AeneasFieldArithmetic.Generated.Funs
import AeneasFieldArithmetic.Proofs.AeneasUtils
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log

/-! # Binary GCD loop for modular inversion

Verifies `gcd_inversion_prime_field_32`, a binary GCD that, given `a0` coprime to
`P = 2^31 - 1`, computes `v` such that `v · a0 ≡ 2^60 (mod P)` with `|v| ≤ 2^60`.
The caller then divides by `2^60` in the field to obtain `a0⁻¹`.

The main result is `gcd_inversion_spec`: the function returns `.ok v` satisfying the
postcondition above. The proof proceeds by showing a loop invariant is preserved
across 60 iterations, with a bit-length termination measure. -/

open Aeneas Aeneas.Std aeneas_field_arithmetic

/-! ## Arithmetic helpers -/

/-- Halving an even number decreases its bit-length by exactly one. -/
theorem size_half_even {n : ℕ} (hn : n ≠ 0) (heven : n % 2 = 0) :
    Nat.size (n / 2) = Nat.size n - 1 := by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    have := Nat.lt_size_self n
    have := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    have : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      conv_lhs => rw [show Nat.size n = (Nat.size n - 1) + 1 from by omega]
      rw [pow_succ, mul_comm]
    omega
  · suffices Nat.size n ≤ Nat.size (n / 2) + 1 by omega
    apply Nat.size_le.mpr
    have := Nat.lt_size_self (n / 2)
    have : n = 2 * (n / 2) := by omega
    have : 2 ^ (Nat.size (n / 2) + 1) = 2 * 2 ^ Nat.size (n / 2) := by
      rw [pow_succ, mul_comm]
    omega

/-- At loop termination (`i = 60`), the invariant gives `Nat.size a + Nat.size b ≤ 2`.
Under coprimality and oddness of `b`, this forces `b = 1`. -/
theorem size_terminal {a b : ℕ} (h_sum : Nat.size a + Nat.size b ≤ 2)
    (h_gcd : Nat.gcd a b = 1) (h_odd : b % 2 = 1) : b = 1 := by
  have := Nat.size_pos.mpr (by omega : 0 < b)
  have : b < 2^2 :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  by_cases hb3 : b = 3
  · subst hb3
    have : Nat.size 3 = 2 := by decide
    have : a = 0 := Nat.size_eq_zero.mp (by omega)
    simp [this] at h_gcd
  · omega

/-- Dividing the even operand by 2 preserves gcd when the other is odd. -/
theorem gcd_half_odd (a b : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 1) :
    Nat.gcd (a / 2) b = Nat.gcd a b := by
  conv_rhs => rw [show a = 2 * (a / 2) from by omega]
  exact (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hb)
    |>.gcd_mul_left_cancel (a / 2)).symm

/-- Doubling the power in a congruence: if x·2^i ≡ w·a0 (mod P), then x·2^(i+1) ≡ 2w·a0. -/
theorem congruence_double (x : ℕ) (w : ℤ) (i a0 : ℕ)
    (h : (↑x * 2^i - w * ↑a0) % (↑P : ℤ) = 0) :
    ((↑x : ℤ) * 2^(i+1) - 2 * w * ↑a0) % ↑P = 0 := by
  have : (↑x : ℤ) * 2^(i+1) - 2 * w * ↑a0 = 2 * (↑x * 2^i - w * ↑a0) := by
    rw [pow_succ]; ring
  rw [this, Int.mul_emod, h, mul_zero, Int.zero_emod]

/-- Subtracting and halving congruences: combines two relations into one at the next power. -/
theorem congruence_half_sub (x y : ℕ) (wx wy : ℤ) (i a0 : ℕ)
    (hle : y ≤ x) (heven : (x - y) % 2 = 0)
    (hx : (↑x * 2^i - wx * ↑a0) % (↑P : ℤ) = 0)
    (hy : (↑y * 2^i - wy * ↑a0) % (↑P : ℤ) = 0) :
    ((↑((x - y) / 2) : ℤ) * 2^(i+1) - (wx - wy) * ↑a0) % ↑P = 0 := by
  have h_eq : (↑((x - y) / 2) : ℤ) * 2 = ↑(x - y) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)
  conv_lhs => rw [pow_succ, show (2 : ℤ)^i * 2 = 2 * 2^i from by ring, ← mul_assoc, h_eq]
  have : (↑(x - y) : ℤ) * 2^i - (wx - wy) * ↑a0 =
      (↑x * 2^i - wx * ↑a0) - (↑y * 2^i - wy * ↑a0) := by
    rw [Nat.cast_sub hle]; ring
  rw [this, Int.sub_emod, hx, hy, sub_self, Int.zero_emod]

/-! ## Definitions -/

/-- The Mersenne31 prime. -/
def P : ℕ := 2^31 - 1

/-- Loop state for binary GCD inversion: `(a, b, u, v, i)` where
- `a`, `b` : gcd operands (`a` may be even, `b` stays odd)
- `u`, `v` : satisfy `a·2^i ≡ u·a0` and `b·2^i ≡ v·a0 (mod P)`;
  at termination `b = 1`, giving `v·a0 ≡ 2^60 (mod P)`
- `i` : loop counter (0 to 60)

This must be an `abbrev` (not a `structure`) because the Aeneas-generated loop body
returns the raw tuple type `U32 × U32 × I64 × I64 × U32`. -/
abbrev GcdState := U32 × U32 × I64 × I64 × U32

/-- Loop invariant for the binary GCD inversion. Maintains:
- Bounds on all variables
- Congruences: a·2^i ≡ u·a0 (mod P) and b·2^i ≡ v·a0 (mod P)
- gcd(a,b) = gcd(a0, P) is preserved
- b stays odd throughout
- Total bit-length of (a,b) decreases towards termination -/
def gcd_loop_inv (a0 : ℕ) (s : GcdState) : Prop :=
  let (a, b, u, v, i) := s
  UScalar.val i ≤ 60 ∧ UScalar.val a < 2^31 ∧ UScalar.val b < 2^31 ∧
  (IScalar.val u).natAbs ≤ 2^(UScalar.val i) ∧
  (IScalar.val v).natAbs ≤ 2^(UScalar.val i) ∧
  ((↑(UScalar.val a) : ℤ) * 2^(UScalar.val i) - IScalar.val u * ↑a0) % ↑P = 0 ∧
  ((↑(UScalar.val b) : ℤ) * 2^(UScalar.val i) - IScalar.val v * ↑a0) % ↑P = 0 ∧
  Nat.gcd (UScalar.val a) (UScalar.val b) = Nat.gcd a0 P ∧
  UScalar.val b % 2 = 1 ∧
  Nat.size (UScalar.val a) + Nat.size (UScalar.val b) ≤ 62 - UScalar.val i

/-- Postcondition: v·a0 ≡ 2^60 (mod P), with |v| ≤ 2^60. -/
def gcd_post (a0 : ℕ) (v : I64) : Prop :=
  (IScalar.val v * ↑a0 - 2^60) % (↑P : ℤ) = 0 ∧ (IScalar.val v).natAbs ≤ 2^60

/-- gcd_post implies the product identity in ZMod -/
theorem gcd_post_mul_eq_zmod (a0 : ℕ) (v : I64) (hpost : gcd_post a0 v) :
    (IScalar.val v : ZMod (2^31-1)) * (a0 : ZMod (2^31-1)) = (2^60 : ZMod (2^31-1)) := by
  have h := hpost.1; rw [show (P : ℤ) = (2^31 - 1 : ℤ) from by simp [P]] at h
  have : ((IScalar.val v * ↑a0 - 2^60 : ℤ) : ZMod (2^31-1)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero h)
  apply sub_eq_zero.mp; push_cast at this; exact this

/-- Termination measure: 60 - i decreases each iteration. -/
def gcd_measure : GcdState → ℕ
  | (_, _, _, _, i) => 60 - UScalar.val i

/-! ## Loop invariant proofs -/

/-- The initial state (a0, P, 1, 0, 0) satisfies the loop invariant. -/
theorem gcd_inv_init (a0 : U32) (h_a0_lt : UScalar.val a0 < 2^31 - 1) :
    gcd_loop_inv (UScalar.val a0) (a0, ⟨2147483647#32⟩, 1#i64, 0#i64, 0#u32) := by
  unfold gcd_loop_inv P; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (0 : ℕ) ≤ 60; omega
  · exact h_a0_lt.le.trans_lt (by omega)
  · change (2147483647 : ℕ) < 2^31; omega
  · change (1 : ℤ).natAbs ≤ 2^(0 : ℕ); simp
  · change (0 : ℤ).natAbs ≤ 2^(0 : ℕ); simp
  · change ((↑(UScalar.val a0) : ℤ) * 2^(0:ℕ) - 1 * ↑(UScalar.val a0)) % ↑(2^31-1:ℕ) = 0
    ring_nf; simp
  · change ((2147483647 : ℤ) * 2^(0:ℕ) - 0 * ↑(UScalar.val a0)) % ↑(2^31-1:ℕ) = 0; simp
  · change Nat.gcd (UScalar.val a0) 2147483647 = Nat.gcd (UScalar.val a0) (2^31-1); norm_num
  · change 2147483647 % 2 = 1; norm_num
  · change Nat.size (UScalar.val a0) + Nat.size 2147483647 ≤ 62 - 0
    have : Nat.size 2147483647 = 31 := by decide
    have := Nat.size_le.mpr (by omega : UScalar.val a0 < 2^31); omega

/-- One iteration of the loop body preserves the invariant and decreases the measure,
or produces the final result satisfying gcd_post.
Three cases: a odd with a < b (swap and subtract),
a odd with a ≥ b (subtract), a even (halve a).
- `a0` : original input whose inverse is being computed
- `a`, `b` : current gcd operands
- `u`, `v` : congruence coefficients (see `gcd_loop_inv`)
- `i` : loop counter -/
theorem gcd_loop_body_spec (a0 : ℕ) (a b : U32) (u v : I64) (i : U32)
    (h_inv : gcd_loop_inv a0 (a, b, u, v, i)) (h_coprime : Nat.gcd a0 P = 1) :
    util.gcd_inversion_prime_field_32_loop.body
      31#u32 a b u v i ⦃ r =>
      match r with
      | .done y => gcd_post a0 y
      | .cont x' => gcd_loop_inv a0 x' ∧ gcd_measure x' < gcd_measure (a, b, u, v, i) ⦄ := by
  simp only [gcd_loop_inv] at h_inv
  obtain ⟨h_i, h_a, h_b, h_u_bound, h_v_bound,
    h_cong_a, h_cong_b, h_gcd, h_b_odd, h_bitlen⟩ := h_inv
  simp only [util.gcd_inversion_prime_field_32_loop.body, step_simps]
  let* ⟨ i1, i1_post ⟩ ← U32.mul_spec
  let* ⟨ i2, i2_post1, i2_post2 ⟩ ← U32.sub_spec
  spec_split
  · -- i < 60: continue
    let* ⟨ i3, i3_post1, _ ⟩ ← UScalar.and_spec
    have h_a_mod : UScalar.val i3 = UScalar.val a % 2 := by
      rw [i3_post1]; change (a.bv &&& 1#32).toNat = a.bv.toNat % 2
      simp [BitVec.toNat_and, Nat.and_one_is_mod]
    have h_i_lt : UScalar.val i < 60 := by scalar_tac
    spec_split
    · -- a is odd
      have h_a_odd : UScalar.val a % 2 = 1 := by rw [← h_a_mod]; scalar_tac
      spec_split
      · -- swap (a < b)
        let* ⟨ a3, a3_post1, _ ⟩ ← U32.sub_spec
        let* ⟨ u3, u3_post ⟩ ← I64.sub_spec
        · exact (I64.sub_in_bounds _ _
            (le_trans h_u_bound (Nat.pow_le_pow_right (by norm_num) h_i))
            (le_trans h_v_bound (Nat.pow_le_pow_right (by norm_num) h_i))).1
        · exact (I64.sub_in_bounds _ _
            (le_trans h_u_bound (Nat.pow_le_pow_right (by norm_num) h_i))
            (le_trans h_v_bound (Nat.pow_le_pow_right (by norm_num) h_i))).2
        let* ⟨ a2, _, _ ⟩ ← U32.ShiftRight_IScalar_spec
        let* ⟨ v2, v2_post ⟩ ← I64.shl_1_spec
        let* ⟨ i4, i4_post1 ⟩ ← U32.add_spec
        have h_a_lt_b : UScalar.val a < UScalar.val b := by scalar_tac
        have h_v2 : IScalar.val v2 = 2 * IScalar.val u := by
          simp only [IScalar.val, v2_post]
          exact I64.shl_1_val u (le_trans h_u_bound (Nat.pow_le_pow_right (by norm_num) (by omega)))
        have h_a2 : UScalar.val a2 = UScalar.val a3 / 2 := by scalar_tac
        have h_sub_even : (UScalar.val b - UScalar.val a) % 2 = 0 := by omega
        refine ⟨⟨by omega, by rw [h_a2, a3_post1]; omega, h_a,
            ?_, ?_, ?_, ?_, ?_, h_a_odd, ?_⟩,
          by simp only [gcd_measure]; rw [i4_post1]; omega⟩
        · rw [i4_post1, u3_post]
          exact (Int.natAbs_sub_le _ _).trans
            ((Nat.add_le_add h_v_bound h_u_bound).trans_eq (by ring))
        · rw [i4_post1, h_v2, pow_succ, mul_comm, Int.natAbs_mul]; simp; exact h_u_bound
        · rw [h_a2, a3_post1, i4_post1, u3_post]
          exact congruence_half_sub _ _ _ _ _ _ (by omega) h_sub_even h_cong_b h_cong_a
        · rw [i4_post1, h_v2]; exact congruence_double _ _ _ _ h_cong_a
        · rw [h_a2, a3_post1, gcd_half_odd _ _ h_sub_even h_a_odd,
            Nat.gcd_sub_self_left (by omega), Nat.gcd_comm]
          exact h_gcd
        · rw [h_a2, a3_post1, i4_post1]
          have h_ne : UScalar.val b - UScalar.val a ≠ 0 := by omega
          have := size_half_even h_ne h_sub_even
          have := Nat.size_le_size (Nat.sub_le (UScalar.val b) (UScalar.val a))
          have := Nat.size_pos.mpr (Nat.pos_of_ne_zero h_ne)
          omega
      · -- no swap (a >= b)
        let* ⟨ a3, a3_post1, _ ⟩ ← U32.sub_spec
        let* ⟨ u3, u3_post ⟩ ← I64.sub_spec
        · exact (I64.sub_in_bounds _ _
            (le_trans h_v_bound (Nat.pow_le_pow_right (by norm_num) h_i))
            (le_trans h_u_bound (Nat.pow_le_pow_right (by norm_num) h_i))).1
        · exact (I64.sub_in_bounds _ _
            (le_trans h_v_bound (Nat.pow_le_pow_right (by norm_num) h_i))
            (le_trans h_u_bound (Nat.pow_le_pow_right (by norm_num) h_i))).2
        let* ⟨ a2, _, _ ⟩ ← U32.ShiftRight_IScalar_spec
        let* ⟨ v2, v2_post ⟩ ← I64.shl_1_spec
        let* ⟨ i4, i4_post1 ⟩ ← U32.add_spec
        have h_a_ge_b : UScalar.val b ≤ UScalar.val a := by scalar_tac
        have h_v2 : IScalar.val v2 = 2 * IScalar.val v := by
          simp only [IScalar.val, v2_post]
          exact I64.shl_1_val v (le_trans h_v_bound (Nat.pow_le_pow_right (by norm_num) (by omega)))
        have h_a2 : UScalar.val a2 = UScalar.val a3 / 2 := by scalar_tac
        have h_sub_even : (UScalar.val a - UScalar.val b) % 2 = 0 := by omega
        refine ⟨⟨by omega, by rw [h_a2, a3_post1]; omega, h_b,
            ?_, ?_, ?_, ?_, ?_, h_b_odd, ?_⟩,
          by simp only [gcd_measure]; rw [i4_post1]; omega⟩
        · rw [i4_post1, u3_post]
          exact (Int.natAbs_sub_le _ _).trans
            ((Nat.add_le_add h_u_bound h_v_bound).trans_eq (by ring))
        · rw [i4_post1, h_v2, pow_succ, mul_comm, Int.natAbs_mul]; simp; exact h_v_bound
        · rw [h_a2, a3_post1, i4_post1, u3_post]
          exact congruence_half_sub _ _ _ _ _ _ (by omega) h_sub_even h_cong_a h_cong_b
        · rw [i4_post1, h_v2]; exact congruence_double _ _ _ _ h_cong_b
        · rw [h_a2, a3_post1, gcd_half_odd _ _ h_sub_even h_b_odd,
            Nat.gcd_sub_self_left (by omega)]
          exact h_gcd
        · rw [h_a2, a3_post1, i4_post1]
          by_cases h_eq : UScalar.val a = UScalar.val b
          · have : UScalar.val b = 1 := by
              rw [h_eq] at h_gcd; simp [Nat.gcd_self] at h_gcd
              rw [h_gcd]; exact h_coprime
            rw [h_eq, Nat.sub_self, this]; simp; omega
          · have h_ne : UScalar.val a - UScalar.val b ≠ 0 := by omega
            have := size_half_even h_ne h_sub_even
            have := Nat.size_le_size (Nat.sub_le (UScalar.val a) (UScalar.val b))
            have := Nat.size_pos.mpr (Nat.pos_of_ne_zero h_ne)
            omega
    · -- a is even
      have h_a_even : UScalar.val a % 2 = 0 := by rw [← h_a_mod]; scalar_tac
      let* ⟨ a2, _, _ ⟩ ← U32.ShiftRight_IScalar_spec
      let* ⟨ v2, v2_post ⟩ ← I64.shl_1_spec
      let* ⟨ i4, i4_post1 ⟩ ← U32.add_spec
      have h_v2 : IScalar.val v2 = 2 * IScalar.val v := by
        simp only [IScalar.val, v2_post]; exact I64.shl_1_val v (h_v_bound.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h_a2 : UScalar.val a2 = UScalar.val a / 2 := by scalar_tac
      refine ⟨⟨by omega, by rw [h_a2]; omega, h_b, ?_, ?_, ?_, ?_, ?_, h_b_odd, ?_⟩,
        by simp only [gcd_measure]; rw [i4_post1]; omega⟩
      · rw [i4_post1]
        exact h_u_bound.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      · rw [i4_post1, h_v2, pow_succ, mul_comm, Int.natAbs_mul]; simp; exact h_v_bound
      · rw [h_a2, i4_post1]
        have : (↑(UScalar.val a / 2) : ℤ) * 2 = ↑(UScalar.val a) := by
          exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_a_even)
        conv_lhs => rw [pow_succ,
          show (2:ℤ)^UScalar.val i * 2 = 2 * 2^UScalar.val i from by ring,
          ← mul_assoc, this]
        exact h_cong_a
      · rw [i4_post1, h_v2]; exact congruence_double _ _ _ _ h_cong_b
      · rw [h_a2, gcd_half_odd _ _ h_a_even h_b_odd]; exact h_gcd
      · rw [h_a2, i4_post1]; by_cases h_a0 : UScalar.val a = 0
        · have : UScalar.val b = 1 := by
            simp [h_a0] at h_gcd; rw [h_gcd]; exact h_coprime
          rw [h_a0, this]; simp; omega
        · have := size_half_even h_a0 h_a_even
          have := Nat.size_pos.mpr (Nat.pos_of_ne_zero h_a0)
          omega
  · -- i >= 60: done
    simp only [step_simps]; unfold gcd_post
    have h_i_eq : UScalar.val i = 60 := (by simp_all; omega)
    have h_b1 : UScalar.val b = 1 :=
      size_terminal (by rw [h_i_eq] at h_bitlen; omega)
        (by rw [h_gcd]; exact h_coprime) h_b_odd
    refine ⟨?_, by rw [h_i_eq] at h_v_bound; exact h_v_bound⟩
    rw [h_i_eq, h_b1] at h_cong_b
    simp only [Nat.cast_one, one_mul] at h_cong_b
    rw [show IScalar.val v * (↑a0 : ℤ) - 2^60 = -(2^60 - IScalar.val v * ↑a0) from by ring]
    exact Int.emod_eq_zero_of_dvd (dvd_neg.mpr (Int.dvd_of_emod_eq_zero h_cong_b))

/-! ## Top-level loop and function specs -/

/-- The full loop terminates and satisfies gcd_post, by well-founded recursion on gcd_measure. -/
theorem gcd_loop_full (a0 : U32) (h_a0_lt : UScalar.val a0 < 2^31 - 1)
    (h_coprime : Nat.gcd (UScalar.val a0) P = 1) :
    util.gcd_inversion_prime_field_32_loop 31#u32 a0 ⟨2147483647#32⟩ 1#i64 0#i64 0#u32
      ⦃ v => gcd_post (UScalar.val a0) v ⦄ := by
  simp only [util.gcd_inversion_prime_field_32_loop]
  apply loop.spec_decr_nat (measure := gcd_measure) (inv := gcd_loop_inv (UScalar.val a0))
  · intro ⟨a, b, u, v, i⟩ h_inv'
    apply WP.spec_mono (gcd_loop_body_spec (UScalar.val a0) a b u v i h_inv' h_coprime)
    intro r hr; cases r <;> exact hr
  · exact gcd_inv_init a0 h_a0_lt

/-- WP spec for the full gcd_inversion_prime_field_32 function (preamble + loop). -/
theorem gcd_inversion_wp (a0 : U32) (h_a0_lt : UScalar.val a0 < 2^31 - 1)
    (h_coprime : Nat.gcd (UScalar.val a0) P = 1) :
    util.gcd_inversion_prime_field_32 31#u32 a0 ⟨2147483647#32⟩
      ⦃ v => gcd_post (UScalar.val a0) v ⦄ := by
  simp only [util.gcd_inversion_prime_field_32]
  let* ⟨ _ ⟩ ← massert_spec
  let* ⟨ i, i_post1, i_post2 ⟩ ← U64.ShiftLeft_spec
  let* ⟨ i1, i1_post1, i1_post2 ⟩ ← U64.sub_spec
  let* ⟨ i2, i2_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ _ ⟩ ← massert_spec
  · show UScalar.val i2 ≤ UScalar.val i1
    have : UScalar.val i = 2147483648 := by
      rw [i_post1]
      simp [U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.shiftLeft_eq]
    have : UScalar.val i2 = 2147483647 := by
      subst i2_post
      simp only [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
      norm_num [UScalar.val]; decide
    omega
  exact gcd_loop_full a0 h_a0_lt h_coprime

/-- Existential form: gcd_inversion returns .ok v satisfying gcd_post. -/
theorem gcd_inversion_spec (a0 : U32) (h_a0_lt : UScalar.val a0 < 2^31 - 1)
    (h_coprime : Nat.gcd (UScalar.val a0) P = 1) :
    ∃ v : I64,
      util.gcd_inversion_prime_field_32 31#u32 a0 ⟨2147483647#32⟩ = .ok v ∧
      gcd_post (UScalar.val a0) v := by
  exact WP.spec_imp_exists (gcd_inversion_wp a0 h_a0_lt h_coprime)
