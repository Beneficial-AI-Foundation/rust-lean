import HornerLean.Spec
import HornerLean.Extracted.Horner_eval_rs
import Hax

namespace HornerLean
/--
Shape, behaviour theorems

if emptiness check returns ok true, result is ok 0.
-/
theorem horner_eval_if_is_empty_ok
  (coeffs : RustSlice i64)
  (x : i64)
  (h : Core_models.Slice.Impl.is_empty i64 coeffs = RustM.ok true) :
  Horner_eval_rs.horner_eval_i64 coeffs x = RustM.ok (0 : i64) := by
  simp [Horner_eval_rs.horner_eval_i64, h]

/-- Base case of the recursion: if `i == 0` (in RustM), return `acc`. -/
theorem horner_rec_zero
  (coeffs : RustSlice i64)
  (x : i64)
  (acc : i64) :
  Horner_eval_rs.horner_rec coeffs x (0 : usize) acc = RustM.ok acc := by
  -- The extracted code branches on `Machine_int.eq i 0`.
  -- With i = 0 this should simp to `pure acc`.
  -- @TODO finish proof
  sorry --simp [Horner_eval_rs.horner_rec]

/--
If the emptiness check returns ok false, `horner_eval_i64` proceeds to the non-empty branch.
This lemma exposes the else-branch shape.
-/
theorem horner_eval_if_is_empty_false_expands
  (coeffs : RustSlice i64)
  (x : i64)
  (h : Core_models.Slice.Impl.is_empty i64 coeffs = RustM.ok false) :
  Horner_eval_rs.horner_eval_i64 coeffs x
    =
  (do
    let n : usize ← Core_models.Slice.Impl.len i64 coeffs
    Horner_eval_rs.horner_rec
      coeffs x
      (← (n -? (1 : usize)))
      (← coeffs[(← (n -? (1 : usize)))]_?)) := by
  simp [Horner_eval_rs.horner_eval_i64, h]

end HornerLean
