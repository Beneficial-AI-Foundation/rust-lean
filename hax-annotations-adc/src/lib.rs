#![cfg_attr(hax, allow(dead_code))]

use core::convert::TryFrom;

// separate functions (just like in Barret example)
// https://github.com/cryspen/hax/blob/main/examples/lean_barrett/src/lib.rs
// this makes easier unfolding in Lean


pub fn adc_pre(a: u32, b: u32, carry: u32) -> bool {
    // carry should be 0 or 1
    carry <= 1
}

pub fn adc_post(a: u32, b: u32, carry: u32, sum: u32, carry_out: u32) -> bool {
    if carry_out > 1 {
        return false;
    }
    let lhs: u64 = a as u64 + b as u64 + carry as u64;
    let rhs: u64 = sum as u64 + ((carry_out as u64) << 32);
    lhs == rhs
}

// this theorem (entered through hax_lib::lean::after) will appear in extracted lean 
// hax_bv_decide automates the proof
#[hax_lib::lean::after(
r#"
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
"#
)]
pub fn adc_u32(a: u32, b: u32, carry: u32) -> (u32, u32) {
    // we do calculations in u64 without overflow
    let tmp: u64 = a as u64 + b as u64 + carry as u64;
    let sum: u32 = tmp as u32;
    let carry_out: u32 = (tmp >> 32) as u32;
    (sum, carry_out)
}
