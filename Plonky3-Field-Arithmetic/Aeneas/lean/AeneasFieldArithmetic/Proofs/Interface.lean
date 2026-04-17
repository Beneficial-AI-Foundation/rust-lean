import Aeneas
import CompPoly.Fields.Mersenne
import AeneasFieldArithmetic.Generated.Funs
import AeneasFieldArithmetic.Proofs.AeneasUtils
import AeneasFieldArithmetic.Proofs.GcdInversion
import CompPoly.Data.Nat.Bitwise
import Mathlib.Data.Nat.Prime.Basic

open Aeneas Aeneas.Std
open aeneas_field_arithmetic mersenne31.Mersenne31

/-! # Notations -/

abbrev m31 := mersenne31.Mersenne31

instance : ToString m31 where
  toString m := Nat.repr m.value.bv.toNat

#eval (⟨⟨⟨2^31 - 1, (by simp)⟩⟩⟩ : m31)

variable (n m : m31)
variable (p q : Mersenne31.Field)

infixl:65 " +ₘ " => mersenne31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add
infixl:70 " ×ₘ " => mersenne31.Mersenne31.Insts.CoreOpsArithMulMersenne31Mersenne31.mul
infixl:70 " /ₘ " => mersenne31.Mersenne31.Insts.CoreOpsArithDivMersenne31Mersenne31.div

/-! # Misc Results

Helper general results

 -/

@[simp]
lemma m31_prime_ok :
  mersenne31.P = Result.ok (⟨2147483647#32⟩ : U32) := by simp [mersenne31.P]; rfl

lemma lt_field_u32 : p.toNat < 2^32 := by cases p; simp; lia

instance : NeZero Mersenne31.fieldSize where
  out := by simp

/-- Helper to locally introduce Field (ZMod (2^31-1)) via have -/
theorem fact_prime_2_31_sub_1 : Fact (Nat.Prime (2^31-1)) :=
  ⟨by rw [show (2^31-1 : ℕ) = Mersenne31.fieldSize from by
    unfold Mersenne31.fieldSize; ring]; exact Mersenne31.is_prime⟩

/-- 2^e = 2^(e % 31) in ZMod (2^31-1) since 2^31 ≡ 1 -/
theorem mersenne_pow_eq (e : ℕ) : (2^e : ZMod (2^31-1)) = (2^(e % 31) : ZMod (2^31-1)) := by
  have h : (2^31 : ZMod (2^31-1)) = 1 := by native_decide
  conv_lhs => rw [show e = e % 31 + 31 * (e / 31) from (Nat.mod_add_div e 31).symm]
  rw [pow_add, pow_mul, h, one_pow, mul_one]

/-- 2^k ≠ 0 in ZMod (2^31-1) -/
theorem pow_two_ne_zero_mersenne (k : ℕ) : (2^k : ZMod (2^31-1)) ≠ 0 := by
  haveI := fact_prime_2_31_sub_1
  exact IsUnit.ne_zero (IsUnit.pow k (Ne.isUnit
    (by change ¬((2 : ℕ) : ZMod (2^31-1)) = 0; rw [ZMod.natCast_eq_zero_iff]; omega)))

/-! # to_m31_spec

Mapping the implementation's `m31` elements to `Mersenne31.Field`

 -/

def to_m31_spec
  (valid_n : UScalar.val n.value ≤ 2^31-1): Mersenne31.Field :=
  if h : UScalar.val n.value < 2^31-1 then
    ⟨↑(n.value), (by grind)⟩
  else 0

postfix:75 "↘" => to_m31_spec

/-- to_m31_spec is injective for elements with val < P -/
theorem to_m31_spec_inj (a b : m31)
    (ha : UScalar.val a.value < 2^31-1) (hb : UScalar.val b.value < 2^31-1)
    (h : to_m31_spec a (le_of_lt ha) = to_m31_spec b (le_of_lt hb)) : a = b := by
  unfold to_m31_spec at h
  rw [dif_pos ha, dif_pos hb] at h
  have h_val : UScalar.val a.value = UScalar.val b.value := by
    have := Fin.mk.inj h; exact_mod_cast this
  cases a; cases b; congr 1; scalar_tac

/-- to_m31_spec always equals Nat.cast in ZMod P (works even when value = P) -/
theorem to_m31_spec_eq_natCast_general (a : m31) (ha : UScalar.val a.value ≤ 2^31-1) :
    to_m31_spec a ha = (UScalar.val a.value : ZMod (2^31-1)) := by
  unfold to_m31_spec
  by_cases h : UScalar.val a.value < 2^31-1
  · rw [dif_pos h]
    exact Fin.ext (by rw [Fin.val_natCast]; exact (Nat.mod_eq_of_lt h).symm)
  · rw [dif_neg h]
    push_neg at h
    have : UScalar.val a.value = 2^31 - 1 := by omega
    rw [this]
    exact (CharP.cast_eq_zero (ZMod (2^31-1)) (2^31-1)).symm

/-! # of_m31_spec

Mapping the specification's `Mersenne31.Field` elements to `m31`

 -/

def of_m31_spec : m31 :=
  {value := Std.U32.ofNatCore p.val (lt_field_u32 p)}

theorem val_of_m31_spec : UScalar.val (of_m31_spec p).value = ZMod.val (p) := by congr

theorem of_m31_spec_lt_m31 : ↑(of_m31_spec p).value < (2^31 - 1 : ℕ) := by
  simp [of_m31_spec]; grind

postfix:50 "↗" => of_m31_spec

theorem to_of_m31_eq:
  (to_m31_spec (of_m31_spec p)
  (by simp only [UScalar.val, of_m31_spec]; grind)) = p := by
  simp [to_m31_spec, of_m31_spec, ZMod.val]

/-! # Addition interface

The following are functions and theorems that allow for a better
interface with the extracted addition.

 -/

/-- The underlying logic of the extracted Mersenne31 `add` implementation -/
def add_logic
  (valid_n : UScalar.val n.value ≤  2^31-1) -- valid m31 elements
  (valid_m : UScalar.val m.value ≤ 2^31-1) : U32 :=
  let nat_sum := UScalar.val n.value + ↑m.value
  -- NOTE: Not <
  if nsh : nat_sum ≤ 2^31 - 1 then @UScalar.ofNatCore .U32 nat_sum (by grind)
  else @UScalar.ofNatCore .U32 (nat_sum - (2^31-1)) (by simp; grind)

-- `2^31 - 1` is a non-canonical zero
#eval add_logic ⟨⟨⟨2^31 - 2, (by simp)⟩⟩⟩ ⟨⟨⟨1, (by simp)⟩⟩⟩
  (by {simp [UScalar.val]}) (by {simp [UScalar.val]})

theorem add_logic_in_bounds
  (valid_n : UScalar.val n.value ≤ 2^31-1) -- valid m31 elements
  (valid_m : UScalar.val m.value ≤ 2^31-1):
  ↑(add_logic n m valid_n valid_m) ≤ (2^31 - 1 : ℕ) := by
  simp [add_logic, UScalar.ofNatCore]; split <;> rename_i h <;>
  simp only [UScalar.val, BitVec.toNat] at *
  · rw [Nat.le_iff_lt_or_eq] at h; cases h <;> grind
  · grind

theorem add_spec
  (valid_n : UScalar.val n.value ≤ 2^31-1) -- valid m31 elements
  (valid_m : UScalar.val m.value ≤ 2^31-1) :
  n +ₘ m = .ok ⟨add_logic n m valid_n valid_m⟩
  := by
  -- Unfold pertinent definitions
  simp [add_logic, Insts.CoreOpsArithAddMersenne31Mersenne31.add]
  split <;> simp [Aeneas.Std.instBindResult, Std.bind, lift] <;>
  simp [Insts.Aeneas_field_arithmeticFieldPrimeField32Mersenne31Mersenne31.ORDER_U32] <;>
  simp [core.num.I32.overflowing_add, IScalar.overflowing_add]
  · -- n + m ≤ 2^31 - 1
    repeat rw [hcast_m31_eq] <;> try grind
    split; grind
    simp [new_reduced, Aeneas.Std.instBindResult, Std.bind]
    rw [Icast_to_U_of_bv_of_int, U32.shr_31_small] <;> try grind
    . simp; rw [UScalar.ofNatCore_add_eq]; grind
    . simp only [UScalar.val]; simp; omega
  · -- 2^31 - 1 < n + m
    rename_i h; simp at h; split <;> try (repeat rw [Ucast_to_I_of_U]; grind)
    simp [core.num.U32.wrapping_sub, UScalar.wrapping_sub]
    rw [Icast_to_U_of_bv_of_int]; repeat rw [Ucast_to_I_of_U]
    repeat rw [Nat.cast_to_bv_of_U_val]
    repeat rw [Ival_of_bv_of_U] <;> try grind
    rw [int_nat_val_dist]
    conv =>
      lhs; rw [UScalar.val_add_eq]
      · skip
      · tactic => grind
    rw [ICast_to_bv_of_Ncast_to_Z_of_N, UScalar.mk_of_Ncast_to_bv_of_bvcast_to_N_of_bv]
    unfold U32.bv; simp
    simp [new_reduced, Aeneas.Std.instBindResult, Std.bind]
    have sum_small : UScalar.val n.value + ↑m.value < (2^32 : ℕ) := by grind
    have sum_sbig : (@UScalar.mk .U32 2147483647#32).bv ≤ n.value.bv + m.value.bv := by
      simp only [LE.le]; grind
    rw [U32.shr_31_small]
    · simp
      have rwn : (2147483647 : ℕ) = (UScalar.val (@UScalar.mk .U32 2147483647#32)) := rfl
      conv =>
        rhs
        pattern _-_
        rw [rwn, UScalar.val_add_eq, UScalar.val, BitVec.toNat_add_of_lt sum_small]
        · skip
        · tactic => simp; grind
      conv => rhs; pattern _+_; rw [←BitVec.toNat_add_of_lt sum_small]
      rw [UScalar.val_add_eq] at sum_small
      · conv => rhs; pattern _-_; rw [←BitVec.toNat_sub_of_le sum_sbig]
        congr
      · simp; grind
    · unfold UScalar.val
      rw [BitVec.toNat_sub_of_le sum_sbig, BitVec.toNat_add_of_lt sum_small]
      grind

/-- Unwraps extracted addition from the result monad -/
def addOk (valid_n : UScalar.val n.value ≤ 2^31-1)
          (valid_m : UScalar.val m.value ≤ 2^31-1) : m31 :=
  match h : n +ₘ m with
  | .ok res => res
  | .fail _ => by rw [add_spec] at h <;> grind
  | .div => by rw [add_spec] at h <;> grind

/--
`addOk` results will always be in the Mersenne31 prime field

**NOTE**: This is provided that `addOk n m ≠ 2^31 - 1`
-/
theorem addOk_in_bounds
  (valid_n : UScalar.val n.value ≤ 2^31-1) -- valid m31 elements
  (valid_m : UScalar.val m.value ≤ 2^31-1) :
  ↑(addOk n m valid_n valid_m).value ≤ (2 ^ 31 - 1 : ℕ) := by
  simp [addOk]; split <;> rename_i h <;> rw [add_spec] at h
  any_goals assumption
  any_goals contradiction
  simp at h; simp [←h]; apply add_logic_in_bounds

/-! # `from_u62` interface

The following are functions and theorems that allow for a better
interface with the `from_u62` function.

This function converts `u62` integers into `m31` elements by wrapping
them over the Mersenne 31 prime.

-/
@[simp]
lemma srh64_1_62 : 1#u64 <<< 62#i32 = .ok (2^62)#u64 := rfl
@[simp]
lemma srh64_1_31 : 1#u64 <<< 31#i32 = .ok (2^31)#u64 := rfl
@[simp]
lemma srh32_1_31 : 1#u32 <<< 31#i32 = .ok (2^31)#u32 := rfl
@[simp] -- For some reason `.ok` doesn't suffice here
lemma sub64_2_pow31_1 : (2147483648#u64 - 1#u64) = Result.ok (2147483647#u64) := rfl
@[simp] -- For some reason `.ok` doesn't suffice here
lemma sub32_2_pow31_1 : (2 ^ 31)#u32 - 1#u32 = Result.ok (2147483647#u32) := rfl

def m31_of_u64 (n : U64) : Result m31 :=
  Result.ok ⟨
    U32.ofNatCore ((UScalar.val n % 2^31 + UScalar.val n / 2^31) % (2^31) +
    (Bool.toNat (decide (UScalar.val n % 2^31 + UScalar.val n / 2^31 > 2^31 - 1))))
    (by {
      by_cases ((UScalar.val n % 2^31 + UScalar.val n / 2^31) > 2^31 - 1)
      <;> simp [UScalarTy.numBits] <;> grind
    })
  ⟩

theorem from_u62_spec (n : U64)
  (n_valid : UScalar.val n < 2^62) :
  mersenne31.from_u62 n = m31_of_u64 n := by
  simp [mersenne31.from_u62, m31_of_u64]; simp at n_valid
  simp [Aeneas.Std.instBindResult, Std.bind, n_valid]
  simp only [HAnd.hAnd, UScalar.and, AndOp.and]; rw [BitVec.and]
  have n_rw : (2147483647 : ℕ) = 2^31 - 1 := rfl
  split <;> rename_i h <;> simp [lift] at h
  conv_lhs at h =>
    congr; congr; rw [n_rw]; rw [Nat.and_two_pow_sub_one_eq_mod]
  simp [lift, HShiftRight.hShiftRight, UScalar.shiftRight_IScalar]
  simp [UScalar.shiftRight, BitVec.ushiftRight]
  simp [new_reduced, Aeneas.Std.instBindResult, Std.bind]
  rw [U32.shr_31_small] <;>
  try (simp [←h]; simp [UScalar.cast]; unfold UScalar.val; grind)
  simp
  rw [U32.shr_31_small] <;>
  try (simp [UScalar.cast]; unfold UScalar.val; simp; omega)
  simp
  conv=>
    lhs; rw [add_spec, add_logic]
    · simp only [←h]
    · tactic=>
        simp only [←h]
        simp [UScalar.cast]; unfold UScalar.val
        simp; grind
    · tactic=>
        simp [UScalar.cast]; unfold UScalar.val
        simp; omega
  congr; split <;> rename_i h2
  · revert h2; simp only [UScalar.cast, UScalar.val, UScalar.ofNatCore]
    simp only [BitVec.zeroExtend_eq_setWidth]
    simp only [BitVec.setWidth, UScalarTy.numBits]
    split; contradiction
    conv=> lhs; congr; simp
    intro h2; simp [Nat.shiftRight_eq_div_pow] at *
    simp [U32.ofNatCore, UScalar.ofNatCore]
    conv=>
      lhs; rw [Nat.mod_eq_of_lt]
      · skip
      · tactic=> grind
    repeat (rw [@Nat.mod_eq_of_lt _ 4294967296] at h2 <;> try grind)
  · revert h2; simp only [UScalar.cast, UScalar.val, UScalar.ofNatCore]
    simp only [BitVec.zeroExtend_eq_setWidth]
    simp only [BitVec.setWidth, UScalarTy.numBits]
    split; contradiction
    conv=> lhs; congr; simp
    intro h2
    conv=> lhs; congr; simp
    conv=> rhs; simp [U32.ofNatCore, UScalar.ofNatCore]
    simp [Nat.shiftRight_eq_div_pow]
    simp [Nat.shiftRight_eq_div_pow] at h2
    repeat (rw [@Nat.mod_eq_of_lt _ 4294967296] at h2 <;>
    try (refine (Nat.lt_trans (Nat.mod_lt _) ?_)))
    any_goals omega
    conv=>
      rhs
      simp [decide, Nat.decLt, Nat.decLe]
      tactic=> split <;> simp <;> try lia
    conv=>
        rhs
        rw [←Nat.mod_add_mod, Nat.mod_eq]
    simp; split <;> lia

/-- Key insight about modular decomposition in the Mersenne31 prime field -/
theorem m31_mod_red (n : ℕ) :
  n % (2 ^ 31 - 1) = (n % (2^31) + n / (2^31)) % (2^31 - 1) := by grind

/-- Useful niche modular equality. Could be generalized -/
lemma m31_swap_mods (n : ℕ)
  (n_range_inf : 2^31 - 1 < n)
  (n_range_sup : n < 2*(2^31 - 1)):
  n % (2^31 - 1) = n % 2^31 + 1 := by omega

/-. Succint logic of the `m31_of_u64` function -/
def m31_of_u64_logic (n : U64) : m31 :=
  let decomp := UScalar.val n % 2147483648 + ↑n / 2147483648
  if decomp % (2^31 - 1) = 0 ∧ decomp ≠ 0 then
    ⟨U32.ofNatCore (2^31-1) (by simp)⟩
  else
    ⟨U32.ofNatCore ((UScalar.val n % (2^31 - 1))) (by grind)⟩

theorem m31_of_u64_spec (n : U64)
  (n_62 : UScalar.val n < 2^62) :
  m31_of_u64 n = .ok (m31_of_u64_logic n) := by
  simp [m31_of_u64_logic]
  let decomp := UScalar.val n % 2147483648 + ↑n / 2147483648
  have decomp_bound : UScalar.val n % 2147483648 + ↑n / 2147483648 ≤ 2*(2^31 - 1) := by grind
  simp_all
  split
  · simp [m31_of_u64]; congr; simp [decide, Nat.decLt, Nat.decLe]
    split
    · simp; have : decomp = 4294967294 := by grind
      rw [←Nat.mod_add_mod]; simp [decomp] at this; rw [this]
    · simp_all; rename_i h; simp at h
      have : decomp = 2147483647 := by grind
      simp_all [decomp]; rw [←Nat.mod_add_mod]; grind
  · simp [m31_of_u64]; congr; simp [decide, Nat.decLt, Nat.decLe]
    split <;> simp_all
    · rw [←Nat.mod_add_mod]; have := m31_swap_mods
      simp at this; rw [←this]
      have := m31_mod_red; simp at this; rw [←this]
      · grind
      · have := Nat.lt_or_eq_of_le decomp_bound; simp at this
        cases this <;> grind
    · simp_all; rw [←Nat.mod_add_mod]
      rename_i h _
      apply Nat.le_pred_of_lt at h; simp at h
      apply Nat.lt_or_eq_of_le at h; cases h <;> grind


/-! # Multiplication interface

The following are functions and theorems that allow for a better
interface with the extracted multiplication.

-/

/-- Function distilling the logic of Mersenne31 multiplication -/
def mul_logic : Result m31 :=
  let n_cast := UScalar.cast .U64 n.value
  let m_cast := UScalar.cast .U64 m.value
  do .ok (m31_of_u64_logic (←n_cast * m_cast))

theorem mul_spec
  (valid_n : UScalar.val n.value ≤ 2^31-1)
  (valid_m : UScalar.val m.value ≤ 2^31-1) :
  n ×ₘ m = mul_logic n m  := by
  have prod_small : ↑n.value * ↑m.value < (2^62 : ℕ) := by grind
  simp [mersenne31.Mersenne31.Insts.CoreOpsArithMulMersenne31Mersenne31.mul]
  simp [mul_logic, Aeneas.Std.instBindResult, Std.bind, lift]
  simp [HMul.hMul, UScalar.mul]
  simp [Mul.mul, UScalar.tryMk,UScalar.tryMkOpt]
  simp at prod_small
  split <;> try rfl
  rename_i h
  split at h <;> rename_i h2 <;> split at h2 <;> try grind
  simp_all
  rw [from_u62_spec] <;> try simp only [UScalar.val]; grind
  rw [m31_of_u64_spec]; grind

/-- Function distilling the logic of Mersenne31 multiplication
    in terms of projecting the elements into ℕ -/
def mul_logic_nat : m31 :=
  m31_of_u64_logic (@UScalar.ofNatCore .U64 (UScalar.val n.value * ↑m.value) (by simp; grind))

theorem mul_logic_nat_eq
  (valid_n : UScalar.val n.value ≤ 2^31-1)
  (valid_m : UScalar.val m.value ≤ 2^31-1) :
  mul_logic n m = .ok (mul_logic_nat n m) := by
  have prod_small : ↑n.value * ↑m.value < (2^62 : ℕ) := by grind
  simp [mul_logic, mul_logic_nat, Aeneas.Std.instBindResult, Std.bind]
  simp [HMul.hMul, UScalar.mul]
  simp [Mul.mul, UScalar.tryMk,UScalar.tryMkOpt]
  simp at prod_small
  aesop (add safe (by omega))

theorem mul_spec_nat
  (valid_n : UScalar.val n.value ≤ 2^31-1)
  (valid_m : UScalar.val m.value ≤ 2^31-1) :
  n ×ₘ m = .ok (mul_logic_nat n m) := by
  rw [mul_spec, mul_logic_nat_eq] <;> grind

/--
  Unwraps extracted addition from the result monad
-/
def mulOk (valid_n : UScalar.val n.value ≤ 2^31-1)
          (valid_m : UScalar.val m.value ≤ 2^31-1) : m31 :=
  match h : n ×ₘ m with
  | .ok res => res
  | .fail _ => by rw [mul_spec_nat] at h <;> grind
  | .div => by
      rw [mul_spec, mul_logic] at h <;> assumption

theorem mulOk_in_bounds
  (valid_n : UScalar.val n.value ≤ 2^31-1)
  (valid_m : UScalar.val m.value ≤ 2^31-1) :
  ↑(mulOk n m valid_n valid_m).value ≤ (2^31 - 1 : ℕ) := by
  simp [mulOk]; split <;> try grind
  rename_i h; rw [mul_spec, mul_logic] at h <;> try assumption
  revert h
  simp [Aeneas.Std.instBindResult, Std.bind]
  simp [HMul.hMul, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt]
  have : Mul.mul (UScalar.val n.value) ↑m.value < 18446744073709551616 := by simp [Mul.mul]; grind
  split <;>  rename_i h <;> split at h <;> rename_i h2 <;> split at h2
  any_goals contradiction
  simp [m31_of_u64_logic]; aesop (add safe (by omega))

theorem mul_logic_nat_in_bounds  :
  ↑(mul_logic_nat n m).value ≤ (2^31 - 1 : ℕ) := by
  simp [mul_logic_nat, m31_of_u64_logic]; split <;> grind

/-! # `new_reduced` interface -/

theorem new_reduced_ok (v : U32) (h : UScalar.val v < 2^31) :
  mersenne31.Mersenne31.new_reduced v = .ok ⟨v⟩ := by
  simp [mersenne31.Mersenne31.new_reduced, Aeneas.Std.instBindResult, Std.bind]
  rw [U32.shr_31_small v h]
  simp [massert]

theorem from_canonical_unchecked_ok (v : U32) (h : UScalar.val v < 2^31 - 1) :
  Insts.Aeneas_field_arithmeticFieldQuotientMapU32.from_canonical_unchecked v =
    .ok ⟨v⟩ := by
  unfold Insts.Aeneas_field_arithmeticFieldQuotientMapU32.from_canonical_unchecked
  rw [Insts.Aeneas_field_arithmeticFieldPrimeField32Mersenne31Mersenne31.ORDER_U32, m31_prime_ok]
  simp only [Aeneas.Std.instBindResult, Std.bind]
  have h_cmp : (↑v : ℕ) < ↑(2147483647#32#uscalar : UScalar .U32) := by
    change UScalar.val v < 2147483647; exact h
  simp [massert, h_cmp]
  exact new_reduced_ok v (by omega)

/-! # Negation interface -/

/-- `neg` succeeds for valid m31 elements, with value `P - n.value` -/
theorem neg_full (valid_n : UScalar.val n.value ≤ 2^31 - 1) :
    ∃ result : m31,
      Insts.CoreOpsArithNegMersenne31.neg n = .ok result ∧
      UScalar.val result.value ≤ 2^31 - 1 ∧
      UScalar.val result.value = 2147483647 - UScalar.val n.value := by
  unfold Insts.CoreOpsArithNegMersenne31.neg
  rw [Insts.Aeneas_field_arithmeticFieldPrimeField32Mersenne31Mersenne31.ORDER_U32, m31_prime_ok]
  simp only [Aeneas.Std.instBindResult, Std.bind]
  have h_ge : UScalar.val n.value ≤ UScalar.val (⟨2147483647#32⟩ : U32) := by
    change UScalar.val n.value ≤ 2147483647; omega
  obtain ⟨diff, h_diff_ok, h_diff_val, _⟩ :=
    (WP.spec_equiv_exists _ _).mp (UScalar.sub_spec h_ge)
  change UScalar.val diff = 2147483647 - UScalar.val n.value at h_diff_val
  simp only [h_diff_ok]
  rw [new_reduced_ok diff (by omega)]
  refine ⟨⟨diff⟩, rfl, ?_, h_diff_val⟩
  change UScalar.val diff ≤ 2147483647; omega

/-! # `from_int_u64` interface

Converts a `U64` into an `m31` element by reducing modulo `P`.
Computes `v % P`, then casts the result down to `U32` via `from_canonical_unchecked`.

-/

theorem cast_u64_u32_val (x : U64) (h : UScalar.val x < 2^32) :
    UScalar.val (UScalar.cast UScalarTy.U32 x) = UScalar.val x := by
  rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt h

/-- `from_int_u64` succeeds and the result value equals `v % P` -/
theorem from_int_u64_full (v : U64) :
    ∃ result : m31,
      Insts.Aeneas_field_arithmeticFieldQuotientMapU64.from_int v = Result.ok result ∧
      UScalar.val result.value = UScalar.val v % 2147483647 ∧
      UScalar.val result.value ≤ 2^31 - 1 := by
  have P_u64_val :
    UScalar.val (UScalar.cast UScalarTy.U64 (⟨2147483647#32⟩ : U32)) = 2147483647 := by
    rw [UScalar.cast_val_eq]; decide
  unfold Insts.Aeneas_field_arithmeticFieldQuotientMapU64.from_int
  simp only [Insts.Aeneas_field_arithmeticFieldPrimeField32Mersenne31Mersenne31.ORDER_U32,
    m31_prime_ok, Aeneas.Std.instBindResult, Std.bind, lift]
  obtain ⟨r, hr, hr_val⟩ := WP.spec_imp_exists (UScalar.rem_spec v (by rw [P_u64_val]; omega))
  rw [hr]; simp only []
  have h_r_lt : UScalar.val r < 2147483647 := by rw [hr_val, P_u64_val]; exact Nat.mod_lt _ (by omega)
  have h_cast_lt : UScalar.val (UScalar.cast UScalarTy.U32 r) < 2^31 - 1 := by
    rw [cast_u64_u32_val r (by omega)]; exact h_r_lt
  rw [from_canonical_unchecked_ok _ h_cast_lt]
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [cast_u64_u32_val r (by omega), hr_val, P_u64_val]
  · show UScalar.val (UScalar.cast UScalarTy.U32 r) ≤ _; omega

/-! # `from_int_i64` interface

Converts an `I64` into an `m31` element.
Positive values are cast to `U64` and handled by `from_int_u64`.
Negative values are negated first, converted via `from_int_u64`, then negated in `m31`.

-/

theorem from_int_i64_full (v : I64) (hv : (IScalar.val v).natAbs ≤ 2^60) :
    ∃ result : m31,
      Insts.Aeneas_field_arithmeticFieldQuotientMapI64.from_int v = Result.ok result ∧
      UScalar.val result.value ≤ 2^31 - 1 ∧
      (UScalar.val result.value : ZMod (2^31-1)) = (IScalar.val v : ZMod (2^31-1)) := by
  unfold Insts.Aeneas_field_arithmeticFieldQuotientMapI64.from_int
  simp only [Aeneas.Std.instBindResult, Std.bind]
  by_cases hpos : 0 ≤ IScalar.val v
  · have h_ge : v >= 0#i64 := by scalar_tac
    simp only [h_ge, lift]
    obtain ⟨r, h_ok, h_val, h_bound⟩ := from_int_u64_full (IScalar.hcast .U64 v)
    refine ⟨r, h_ok, h_bound, ?_⟩
    simp only [h_val]
    conv_lhs => rw [show (2147483647 : ℕ) = 2^31-1 from by omega]
    rw [(CharP.natCast_eq_natCast_mod (ZMod (2^31-1)) (2^31-1) _).symm]
    have h_cast_val : (UScalar.val (IScalar.hcast .U64 v) : ℤ) = IScalar.val v := by
      have h_wp := IScalar.hcast_inBounds_spec (src_ty := .I64) .U64 v ⟨hpos, by scalar_tac⟩
      simp [WP.spec_ok, lift] at h_wp; exact h_wp
    rw [← Int.cast_natCast (R := ZMod (2^31-1)) (UScalar.val (IScalar.hcast .U64 v)),
        h_cast_val]
  · have h_neg : ¬(v >= 0#i64) := by scalar_tac
    simp only [h_neg, HNeg.hNeg, IScalar.neg, IScalar.tryMk, IScalar.tryMkOpt, Result.ofOption]
    have hv_neg : IScalar.val v < 0 := by omega
    -- IScalar.neg.step_spec wraps with `lift` so doesn't match bare `-. v` in do blocks;
    -- we unfold through tryMkOpt and resolve the bounds check directly with dif_pos.
    have hcb : IScalar.check_bounds .I64 (-(IScalar.val v)) := by
      have := v.hBounds; simp [IScalar.check_bounds, IScalarTy.I64_numBits_eq]; omega
    rw [dif_pos hcb]; simp only [lift]
    set nv := IScalar.ofIntCore (-(IScalar.val v)) (IScalar.check_bounds_imp_inBounds hcb)
    have hnv_val : IScalar.val nv = -(IScalar.val v) :=
      IScalar.ofInt_val_eq (IScalar.check_bounds_imp_inBounds hcb)
    obtain ⟨m, hm_ok, hm_val, hm_bound⟩ := from_int_u64_full (IScalar.hcast .U64 nv)
    rw [hm_ok]
    obtain ⟨result, hr_ok, hr_bound, hr_val⟩ := neg_full ⟨m.value⟩ hm_bound
    refine ⟨result, hr_ok, hr_bound, ?_⟩
    simp only [hr_val, hm_val]
    conv_lhs => rw [show (2147483647 : ℕ) = 2^31-1 from by omega]
    have h_nv_pos : 0 ≤ IScalar.val nv := by omega
    have h_cast_val : (UScalar.val (IScalar.hcast .U64 nv) : ℤ) = IScalar.val nv := by
      have h_wp := IScalar.hcast_inBounds_spec (src_ty := .I64) .U64 nv
        ⟨h_nv_pos, by scalar_tac⟩
      simp [WP.spec_ok, lift] at h_wp; exact h_wp
    rw [Nat.cast_sub (Nat.mod_lt _ (by omega : (0:ℕ) < 2^31-1)).le,
        CharP.cast_eq_zero (ZMod (2^31-1)) (2^31-1), zero_sub,
        (CharP.natCast_eq_natCast_mod (ZMod (2^31-1)) (2^31-1) _).symm]
    rw [show ((UScalar.val (IScalar.hcast .U64 nv) : ℕ) : ZMod (2^31-1)) =
            ((-IScalar.val v : ℤ) : ZMod (2^31-1)) from by
      rw [← Int.cast_natCast (R := ZMod (2^31-1)) (UScalar.val (IScalar.hcast .U64 nv)),
          h_cast_val, hnv_val]]
    rw [Int.cast_neg, neg_neg]

/-! # `div_2exp_u64` interface

`div_2exp_u64 m exp` divides `m` by `2^(exp % 31)`

-/

/-- Division by 2^k in Mersenne31: the shift-and-recombine decomposition
    `(x / 2^k + x % 2^k * 2^(31-k)) * 2^k ≡ x (mod 2^31-1)`. -/
theorem m31_div_decomp (x k : ℕ) (hk31 : k ≤ 31) :
    ((x / 2^k + x % 2^k * 2^(31 - k)) * 2^k) % (2^31 - 1) = x % (2^31 - 1) := by
  have hpk : (0 : ℕ) < 2^k := Nat.pos_of_ne_zero (by positivity)
  have h_div_mod := Nat.div_add_mod x (2^k)
  have h_exp : (31 - k) + k = 31 := by omega
  have h_eq : (x / 2^k + x % 2^k * 2^(31 - k)) * 2^k = x + x % 2^k * (2^31 - 1) := by
    have h1 : x / 2^k * 2^k + x % 2^k = x := by rw [mul_comm]; exact h_div_mod
    have h2 : x % 2^k * 2^(31 - k) * 2^k = x % 2^k * 2^31 := by
      rw [mul_assoc, ← pow_add, h_exp]
    rw [Nat.add_mul, h2]; omega
  rw [h_eq, Nat.add_mul_mod_self_right]

/-- Bit disjointness: a < 2^n and 2^n ∣ b implies a &&& b = 0 -/
theorem nat_and_eq_zero_of_lt_dvd {a b n : ℕ} (ha : a < 2^n) (hb : 2^n ∣ b) :
    a &&& b = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro i
  simp only [Nat.testBit_and, Bool.and_eq_false_imp]
  intro ha_bit
  have hi : i < n := by
    by_contra h; push_neg at h
    have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) h))
    simp [this] at ha_bit
  obtain ⟨q, hq⟩ := hb
  rw [hq, Nat.testBit_two_pow_mul]
  simp [show ¬(i ≥ n) from by omega]

/-- General `div_2exp_u64` specification: the result is a valid m31 element
    whose value satisfies the rotation identity `result * 2^k ≡ m.value (mod 2^31-1)`
    where `k = exp % 31`. -/
theorem div_2exp_u64_spec (m : m31) (exp : U64) (hm : UScalar.val m.value ≤ 2^31 - 1) :
    Insts.Aeneas_field_arithmeticFieldPrimeCharacteristicRingMersenne31.div_2exp_u64 m exp
    ⦃ result =>
      UScalar.val result.value ≤ 2^31 - 1 ∧
      (UScalar.val result.value * 2^(UScalar.val exp % 31)) % (2^31 - 1) =
        UScalar.val m.value % (2^31 - 1) ⦄ := by
  have hk_lt : UScalar.val exp % 31 < 31 := Nat.mod_lt _ (by omega)
  unfold Insts.Aeneas_field_arithmeticFieldPrimeCharacteristicRingMersenne31.div_2exp_u64
  let* ⟨ i, i_post ⟩ ← U64.rem_spec
  let* ⟨ exp1, exp1_post ⟩ ← UScalar.cast.step_spec
  have h_exp1_val : UScalar.val exp1 = UScalar.val exp % 31 := by
    subst exp1_post; rw [UScalar.cast_val_eq]
    have : UScalarTy.U8.numBits = 8 := rfl
    rw [this, i_post]; exact Nat.mod_eq_of_lt (by omega)
  have h_exp1_lt : UScalar.val exp1 < 31 := by omega
  let* ⟨ left, left_post, _ ⟩ ← U32.ShiftRight_spec
  let* ⟨ i1, i1_post, _ ⟩ ← U8.sub_spec
  let* ⟨ i2, i2_post, _ ⟩ ← U32.ShiftLeft_spec
  let* ⟨ i3, i3_post, _ ⟩ ← U32.ShiftLeft_IScalar_spec
  let* ⟨ i4, _, _ ⟩ ← U32.sub_spec
  let* ⟨ right, right_post, _ ⟩ ← UScalar.and_spec
  let* ⟨ rotated, rotated_post, _ ⟩ ← UScalar.or_spec
  -- Key intermediate values
  have h_left_val : UScalar.val left = UScalar.val m.value / 2^(UScalar.val exp % 31) := by
    rw [left_post, h_exp1_val, Nat.shiftRight_eq_div_pow]
  have h_i3_val : UScalar.val i3 = 2147483648 := by rw [i3_post]; native_decide
  have h_i4_val : UScalar.val i4 = 2^31 - 1 := by
    have : UScalar.val i4 = UScalar.val i3 - 1 := by scalar_tac
    omega
  have h_rotated_or : UScalar.val rotated = UScalar.val left ||| UScalar.val right := by
    rw [rotated_post]; simp [UScalar.val_or]
  -- Bound: rotated < 2^31
  have h_rotated_lt : UScalar.val rotated < 2^31 := by
    rw [h_rotated_or]; apply Nat.or_lt_two_pow
    · rw [h_left_val]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    · have : UScalar.val right ≤ UScalar.val i4 := by
        rw [right_post]; simp [UScalar.val_and]; exact Nat.and_le_right
      omega
  rw [new_reduced_ok rotated h_rotated_lt]
  simp only [WP.spec_ok]
  refine ⟨by omega, ?_⟩
  -- Value: rotation identity
  have h_right_eq : UScalar.val right =
      (UScalar.val m.value % 2^(UScalar.val exp % 31)) * 2^(31 - UScalar.val exp % 31) := by
    have : UScalar.val right = UScalar.val i2 &&& UScalar.val i4 := by
      rw [right_post]; simp [UScalar.val_and]
    rw [this, h_i4_val]
    have : UScalar.val i2 = (UScalar.val m.value * 2^(31 - UScalar.val exp % 31)) % 2^32 := by
      rw [i2_post, show UScalar.val i1 = 31 - UScalar.val exp % 31 from by omega,
          Nat.shiftLeft_eq, U32.size_eq]; norm_num
    rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd]; swap; omega
    conv_lhs => rw [show (2 : ℕ)^31 =
        2^(UScalar.val exp % 31) * 2^(31 - UScalar.val exp % 31) from by
      rw [← pow_add]; congr 1; omega]
    rw [Nat.mul_mod_mul_right]
  -- Bit disjointness → OR = ADD
  have h_left_lt : UScalar.val left < 2^(31 - UScalar.val exp % 31) := by
    rw [h_left_val]; apply Nat.div_lt_of_lt_mul
    calc UScalar.val m.value < 2^31 := by omega
      _ = 2^(UScalar.val exp % 31) * 2^(31 - UScalar.val exp % 31) := by
          rw [← pow_add]; congr 1; omega
  have h_rotated_eq : UScalar.val rotated =
      UScalar.val m.value / 2^(UScalar.val exp % 31) +
      (UScalar.val m.value % 2^(UScalar.val exp % 31)) * 2^(31 - UScalar.val exp % 31) := by
    rw [h_rotated_or,
        ← Nat.sum_of_and_eq_zero_is_or
          (nat_and_eq_zero_of_lt_dvd h_left_lt (by rw [h_right_eq]; exact dvd_mul_left _ _)),
        h_left_val, h_right_eq]
  rw [h_rotated_eq]
  exact m31_div_decomp (UScalar.val m.value) (UScalar.val exp % 31) (by omega)

/-- Lifts div_2exp_u64_spec from ℕ modular arithmetic to ZMod (2^31-1):
    `result * 2^(exp % 31) = m.value` in `ZMod (2^31-1)`. -/
theorem div_2exp_u64_zmod (m_val : m31) (exp : U64)
    (hm : UScalar.val m_val.value ≤ 2^31 - 1)
    (result : m31)
    (h : Insts.Aeneas_field_arithmeticFieldPrimeCharacteristicRingMersenne31.div_2exp_u64 m_val exp = .ok result) :
    (UScalar.val result.value * 2^(UScalar.val exp % 31) : ZMod (2^31-1)) =
      (UScalar.val m_val.value : ZMod (2^31-1)) := by
  obtain ⟨r, hr_ok, _, hr_post⟩ := WP.spec_imp_exists (div_2exp_u64_spec m_val exp hm)
  rw [hr_ok] at h; injection h with h_eq; subst h_eq
  have key : ((UScalar.val r.value * 2^(UScalar.val exp % 31) : ℕ) : ZMod (2^31-1)) =
             ((UScalar.val m_val.value : ℕ) : ZMod (2^31-1)) := by
    conv_lhs => rw [CharP.natCast_eq_natCast_mod (ZMod (2^31-1)) (2^31-1)]
    conv_rhs => rw [CharP.natCast_eq_natCast_mod (ZMod (2^31-1)) (2^31-1)]
    exact congrArg _ hr_post
  push_cast at key
  exact key

