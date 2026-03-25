
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import CoreModelsPatch
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def P3_fri_kernel.compute_log_arity_for_round
  (log_current_height : usize)
  (next_input_log_height : (Core_models.Option.Option usize))
  (log_final_height : usize)
  (max_log_arity : usize)
  : RustM usize
  := do
  let max_fold_to_target : usize ← (log_current_height -? log_final_height);
  let max_fold : usize ←
    match next_input_log_height with
      | (Core_models.Option.Option.None ) => (pure max_fold_to_target)
      | (Core_models.Option.Option.Some next_log_height)
        =>
          let max_fold_to_next : usize ←
            (log_current_height -? next_log_height);
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            max_fold_to_next
            max_fold_to_target)) then
            (pure max_fold_to_next)
          else
            (pure max_fold_to_target);
  if (← (Rust_primitives.Hax.Machine_int.lt max_fold max_log_arity)) then
    (pure max_fold)
  else
    (pure max_log_arity)
