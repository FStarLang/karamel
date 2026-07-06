/// Regression test: ECast on UInt8/UInt16 wrapping arithmetic
/// doesn't mask before widening, leaking overflow bits.
module SmallIntCast

open FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

/// Cast wrapping addition to UInt32.
/// F*: (200 + 56) mod 256 = 0, cast to UInt32 => 0ul.
let cast_add_to_u32 (a b: UInt8.t) : U32.t =
  Cast.uint8_to_uint32 (a +%^ b)

/// Cast wrapping subtraction to UInt32.
/// F*: (0 - 1) mod 256 = 255, cast to UInt32 => 255ul.
let cast_sub_to_u32 (a b: UInt8.t) : U32.t =
  Cast.uint8_to_uint32 (a -%^ b)

/// Cast wrapping multiplication to UInt32.
/// F*: (128 * 3) mod 256 = 128, cast to UInt32 => 128ul.
let cast_mul_to_u32 (a b: UInt8.t) : U32.t =
  Cast.uint8_to_uint32 (a *%^ b)

/// Cast BNot to UInt32.
/// F*: lognot 0x0F = 0xF0 = 240, cast to UInt32 => 240ul.
let cast_bnot_to_u32 (x: UInt8.t) : U32.t =
  Cast.uint8_to_uint32 (UInt8.lognot x)

let main () : FStar.Int32.t =
  if cast_add_to_u32 200uy 56uy = 0ul
  && cast_sub_to_u32 0uy 1uy = 255ul
  && cast_mul_to_u32 128uy 3uy = 128ul
  && cast_bnot_to_u32 0x0Fuy = 240ul
  then 0l
  else 1l
