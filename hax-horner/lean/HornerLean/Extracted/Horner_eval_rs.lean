
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import HornerLean.CoreModelsPatch
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

partial def Horner_eval_rs.horner_rec
  (coeffs : (RustSlice i64))
  (x : i64)
  (i : usize)
  (acc : i64)
  : RustM i64
  := do
  if (← (Rust_primitives.Hax.Machine_int.eq i (0 : usize))) then
    (pure acc)
  else
    let i1 : usize ← (i -? (1 : usize));
    let acc1 : i64 ← ((← (acc *? x)) +? (← coeffs[i1]_?));
    (Horner_eval_rs.horner_rec coeffs x i1 acc1)

def Horner_eval_rs.horner_eval_i64
  (coeffs : (RustSlice i64))
  (x : i64)
  : RustM i64
  := do
  if (← (Core_models.Slice.Impl.is_empty i64 coeffs)) then
    (pure (0 : i64))
  else
    let n : usize ← (Core_models.Slice.Impl.len i64 coeffs);
    (Horner_eval_rs.horner_rec
      coeffs
      x
      (← (n -? (1 : usize)))
      (← coeffs[(← (n -? (1 : usize)))]_?))