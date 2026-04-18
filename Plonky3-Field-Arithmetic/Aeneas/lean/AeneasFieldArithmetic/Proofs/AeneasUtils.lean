import Aeneas

open Aeneas Aeneas.Std

variable (n m : U32)

@[grind =]
theorem hcast_m31_eq (n_small : n < (2^31 : ℕ)) : IScalar.val (UScalar.hcast IScalarTy.I32 n) = UScalar.val n := by
  simp only [IScalar.val, UScalar.val, UScalar.hcast]; grind

theorem UScalar.val_add_eq {ty : UScalarTy} (n m : UScalar ty)
 (inBounds : ↑n + ↑m < (2^(UScalarTy.numBits ty) : ℕ)) : UScalar.val n + UScalar.val m = (n.bv + m.bv).toNat := by
  simp [UScalarTy.numBits, System.Platform.numBits] at *
  cases ty <;> try grind
  cases h: System.Platform.getNumBits (); simp_all
  rename_i p; cases p <;> grind

theorem UScalar.val_sub_eq {ty : UScalarTy} (n m : UScalar ty)
 (inBounds : ↑m < ↑n) : UScalar.val n - UScalar.val m = (n.bv - m.bv).toNat := by
  have nm_small (n : UScalar UScalarTy.Usize) :
    ↑n < (2^((System.Platform.getNumBits ()).1) : ℕ) := by
    cases n; rename_i bv
    simp [UScalarTy.numBits, System.Platform.numBits] at bv
    refine (@BitVec.toNat_lt_twoPow_of_le ↑(System.Platform.getNumBits ())
    ↑(System.Platform.getNumBits ()) (by rfl) _)
  simp [UScalarTy.numBits, System.Platform.numBits] at *
  cases ty <;> grind

theorem UScalar.val_mul_eq {ty : UScalarTy} (n m : UScalar ty)
 (inBounds : ↑n * ↑m < (2^(UScalarTy.numBits ty) : ℕ)) : UScalar.val n * UScalar.val m = (n.bv * m.bv).toNat := by
  simp [UScalarTy.numBits, System.Platform.numBits] at *
  cases ty <;> try grind
  cases h: System.Platform.getNumBits (); simp_all
  rename_i p; cases p <;> grind

theorem int_nat_val_dist :
  @Nat.cast ℤ _ (UScalar.val n) + ↑(UScalar.val m) =
  ↑(UScalar.val n + UScalar.val m) := by simp only [Nat.cast_add]

theorem Icast_to_U_of_bv_of_int (n : ℤ) :
  @IScalar.hcast .I32 UScalarTy.U32 ((BitVec.ofInt 32 n)#iscalar) =
  ⟨n⟩ := by
  simp [IScalar.hcast]; congr

theorem Ucast_to_I_of_U (n : U32) : @UScalar.hcast UScalarTy.U32 IScalarTy.I32 n = ⟨n⟩ := by
  simp [UScalar.hcast]

theorem U32.shr_31_small (u : U32) (h : ↑u < (2^31 : ℕ)) : u >>> 31#i32 = .ok 0#u32 := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  split <;> first | contradiction | (simp [BitVec.ushiftRight]; congr; omega)

theorem UScalar.ofNatCore_add_eq (n m : U32) (inBounds : UScalar.val n + ↑m < (2^32 : ℕ)) :
  @UScalar.ofNatCore .U32 (UScalar.val n + ↑m) (by grind) = ⟨n.bv + m.bv⟩ := by
  congr; grind

theorem Nat.cast_to_bv_of_U_val (n : U32) :
  @Nat.cast (BitVec IScalarTy.I32.numBits) _ (UScalar.val n) = n.bv := by simp

theorem Ival_of_bv_of_U (n : U32) (h : UScalar.val n < 2^31) :
IScalar.val (n.bv#iscalar : I32) = Nat.cast (UScalar.val n) := by
  simp only [IScalar.val, UScalar.val, Nat.cast]; grind

theorem ICast_to_bv_of_Ncast_to_Z_of_N (n : ℕ) :
  @Int.cast (BitVec UScalarTy.U32.numBits) _ (@Nat.cast ℤ _ n) = Nat.cast n
  := by simp

theorem UScalar.mk_of_Ncast_to_bv_of_bvcast_to_N_of_bv {ty : UScalarTy} (b : BitVec ty.numBits) :
  UScalar.mk ↑b.toNat = UScalar.mk b := by simp

/-! ## I64 helpers -/

/-- IScalar.val of a shift-left-by-1 equals 2 * the original value (when in bounds) -/
theorem I64.shl_1_val (v : I64)
    (h_bound : (IScalar.val v).natAbs ≤ 2^59) :
    IScalar.val (⟨v.bv.shiftLeft 1⟩ : I64) = 2 * IScalar.val v := by
  have h_eq : IScalar.val v = v.bv.toInt := rfl
  simp only [IScalar.val]
  change (v.bv <<< 1).toInt = 2 * v.bv.toInt
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.toInt_mul,
      show (BitVec.twoPow 64 1).toInt = 2 from by decide]
  ring_nf; rw [← h_eq]
  apply Arith.Int.bmod_pow2_eq_of_inBounds 63 <;> (rw [h_eq]; norm_num; omega)

/-- I64 subtraction stays in bounds when both operands have natAbs ≤ 2^i and i ≤ 60 -/
theorem I64.sub_in_bounds (u v : ℤ)
    (h_u : u.natAbs ≤ 2^60) (h_v : v.natAbs ≤ 2^60) :
    I64.min ≤ v - u ∧ v - u ≤ I64.max := by
  simp only [I64.min, I64.max, I64.numBits]; norm_num; omega

/-- Step spec for I64 shift left by 1 (via I32 literal) -/
@[step]
theorem I64.shl_1_spec (x : I64) :
  (x <<< (1#i32 : I32)) ⦃ z => z.bv = x.bv.shiftLeft 1 ⦄ := by
  unfold WP.spec
  simp only [HShiftLeft.hShiftLeft, IScalar.shiftLeft_IScalar, IScalar.shiftLeft,
    show (1#i32 : I32).val ≥ 0 from by decide,
    show (1#i32 : I32).toNat = 1 from by simp only [IScalar.toNat]; decide,
    show 1 < IScalarTy.I64.numBits from by simp only [IScalarTy.I64_numBits_eq]; decide,
    ↓reduceIte, WP.theta, WP.wp_return]

