import Aeneas
import CompPoly.Fields.Mersenne
import AeneasFieldArithmetic.Generated.Funs
import AeneasFieldArithmetic.Proofs.AeneasUtils

open Aeneas Aeneas.Std
open aeneas_field_arithmetic mersenne31.Mersenne31

abbrev m31 := mersenne31.Mersenne31

variable (n m : m31)
variable (p q : Mersenne31.Field)

infixl:60 " +ₘ " => mersenne31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add

def to_m31_spec
  (valid_n : UScalar.val n.value < 2^31-1): Mersenne31.Field :=
  ⟨↑(n.value), (by grind)⟩

postfix:75 "↘" => to_m31_spec

lemma lt_field_u32 : p.toNat < 2^32 := by cases p; simp; lia
lemma lt_field_m31 : p.toNat < 2^31 - 1 := by cases p; simp; lia

def new_of_field : Result m31 := new (Std.U32.ofNatCore p.val (lt_field_u32 p))

@[simp]
lemma m31_prime_ok :
  mersenne31.P = Result.ok { bv := ⟨2^31 - 1, (by simp)⟩} := by
    simp [mersenne31.P]; rfl

lemma new_of_field_isOk :
  new_of_field p =
  .ok { value := Std.U32.ofNatCore p.val (lt_field_u32 p) } := by
  simp [new_of_field, new]
  simp [Aeneas.Std.instBindResult, Std.bind]
  simp [HMod.hMod, UScalar.rem]
  dsimp [UScalar.val]; congr; simp
  cases p with | mk p ph
  simp at ph
  simp [Mod.mod, BitVec.umod, ZMod.val]
  congr; omega

def of_m31_spec : m31 :=
  {value := Std.U32.ofNatCore p.val (lt_field_u32 p)}

theorem of_m31_spec_lt_m31 : ↑(of_m31_spec p).value < (2^31 - 1 : ℕ) := by
  simp [of_m31_spec]; grind

postfix:50 "↗" => of_m31_spec

theorem neq_of_field_eq_spec : new_of_field p = .ok (p↗) := by
  simp [of_m31_spec, new_of_field_isOk]

instance : NeZero Mersenne31.fieldSize where
  out := by simp

theorem to_of_m31_eq:
  (to_m31_spec (of_m31_spec p)
  (by simp only [UScalar.val, of_m31_spec]; grind)) = p := by
  simp [to_m31_spec, of_m31_spec, ZMod.val]

theorem field_size_mod_small : p.val % Mersenne31.fieldSize = p.val := by grind

/-- The underlying logic of the extracted Mersenne31 `add` implementation -/
def add_logic
  (valid_n : UScalar.val n.value < 2^31-1) -- valid m31 elements
  (valid_m : UScalar.val m.value < 2^31-1) : U32 :=
  let nat_sum := UScalar.val n.value + ↑m.value
  -- NOTE: Not <
  if nsh : nat_sum ≤ 2^31 - 1 then @UScalar.ofNatCore .U32 nat_sum (by grind)
  else @UScalar.ofNatCore .U32 (nat_sum - (2^31-1)) (by simp; grind)

theorem add_logic_in_bounds
  (valid_n : UScalar.val n.value < 2^31-1) -- valid m31 elements
  (valid_m : UScalar.val m.value < 2^31-1)
  (special_case : UScalar.val n.value + ↑m.value ≠ (2^31-1 : ℕ)):
  ↑(add_logic n m valid_n valid_m) < (2^31 - 1 : ℕ) := by
  simp [add_logic, UScalar.ofNatCore]; split <;> rename_i h <;>
  simp only [UScalar.val, BitVec.toNat] at *
  · rw [Nat.le_iff_lt_or_eq] at h; cases h <;> grind
  · grind

theorem add_spec
  (valid_n : UScalar.val n.value < 2^31-1) -- valid m31 elements
  (valid_m : UScalar.val m.value < 2^31-1) :
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
def addOk (valid_n : UScalar.val n.value < 2^31-1)
          (valid_m : UScalar.val m.value < 2^31-1) : m31 :=
  match h : n +ₘ m with
  | .ok res => res
  | .fail _ => by rw [add_spec] at h <;> grind
  | .div => by rw [add_spec] at h <;> grind

/--
`addOk` results will always be in the Mersenne31 prime field

**NOTE**: This is provided that `addOk n m ≠ 2^31 - 1`
-/
theorem addOk_in_bounds
  (valid_n : UScalar.val n.value < 2^31-1) -- valid m31 elements
  (valid_m : UScalar.val m.value < 2^31-1)
  (special_case : UScalar.val n.value + ↑m.value ≠ (2^31-1 : ℕ)) :
  ↑(addOk n m valid_n valid_m).value < (2 ^ 31 - 1 : ℕ) := by
  simp [addOk]; split <;> rename_i h <;> rw [add_spec] at h
  any_goals assumption
  any_goals contradiction
  simp at h; simp [←h]; apply add_logic_in_bounds; assumption
