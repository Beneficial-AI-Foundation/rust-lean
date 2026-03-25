
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

def Hax_adc_poc.adc_pre (a : u32) (b : u32) (carry : u32) : RustM Bool := do
  (Rust_primitives.Hax.Machine_int.le carry (1 : u32))

def Hax_adc_poc.adc_post
  (a : u32)
  (b : u32)
  (carry : u32)
  (sum : u32)
  (carry_out : u32)
  : RustM Bool
  := do
  if (← (Rust_primitives.Hax.Machine_int.gt carry_out (1 : u32))) then
    (pure false)
  else
    let lhs : u64 ←
      ((← ((← (Rust_primitives.Hax.cast_op a))
          +? (← (Rust_primitives.Hax.cast_op b))))
        +? (← (Rust_primitives.Hax.cast_op carry)));
    let rhs : u64 ←
      ((← (Rust_primitives.Hax.cast_op sum))
        +? (← ((← (Rust_primitives.Hax.cast_op carry_out)) <<<? (32 : i32))));
    (Rust_primitives.Hax.Machine_int.eq lhs rhs)

def Hax_adc_poc.adc_u32
  (a : u32)
  (b : u32)
  (carry : u32)
  : RustM (Rust_primitives.Hax.Tuple2 u32 u32)
  := do
  let tmp : u64 ←
    ((← ((← (Rust_primitives.Hax.cast_op a))
        +? (← (Rust_primitives.Hax.cast_op b))))
      +? (← (Rust_primitives.Hax.cast_op carry)));
  let sum : u32 ← (Rust_primitives.Hax.cast_op tmp);
  let carry_out : u32 ← (Rust_primitives.Hax.cast_op (← (tmp >>>? (32 : i32))));
  (pure (Rust_primitives.Hax.Tuple2.mk sum carry_out))


set_option maxHeartbeats 500000 in
@[spec]
theorem Hax_adc_poc.adc_u32_spec (a b carry : u32) :
  ⦃ ⌜ Hax_adc_poc.adc_pre a b carry = pure true ⌝ ⦄
  Hax_adc_poc.adc_u32 a b carry
  ⦃ ⇓ r => ⌜
      -- r : (u32 × u32)
      Hax_adc_poc.adc_post a b carry r.fst r.snd = pure true
    ⌝ ⦄
:= by
  -- unfold definitions
  unfold Hax_adc_poc.adc_u32 Hax_adc_poc.adc_pre Hax_adc_poc.adc_post
  -- bit-blasting
  hax_bv_decide (timeout := 30)
