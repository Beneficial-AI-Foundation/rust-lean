
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def Horner_eval_rs.horner_eval_i64
  (coeffs : (RustSlice i64))
  (x : i64)
  : RustM i64
  := do
  if (← (Core.Slice.Impl.is_empty i64 coeffs)) then
    (pure (0 : i64))
  else
    let i : usize ← (Core.Slice.Impl.len i64 coeffs);
    let acc : i64 ← coeffs[(← (i -? (1 : usize)))]_?;
    let ⟨acc, i⟩ ←
      (Rust_primitives.Hax.while_loop
        (fun ⟨acc, i⟩ => (do (pure true) : RustM Bool))
        (fun ⟨acc, i⟩ => (do
          (Rust_primitives.Hax.Machine_int.gt i (1 : usize)) : RustM Bool))
        (fun ⟨acc, i⟩ => (do
          (Rust_primitives.Hax.Int.from_machine (0 : u32)) : RustM
          Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple2.mk acc i)
        (fun ⟨acc, i⟩ => (do
          let i : usize ← (i -? (1 : usize));
          let acc : i64 ←
            ((← (acc *? x)) +? (← coeffs[(← (i -? (1 : usize)))]_?));
          (pure (Rust_primitives.Hax.Tuple2.mk acc i)) : RustM
          (Rust_primitives.Hax.Tuple2 i64 usize))));
    (pure acc)