/// Regression test for karamel issue #707.
/// Tests that UInt8/UInt16 switch scrutinee is correctly masked
/// after wrapping arithmetic, so the right branch is taken.
module SmallIntSwitch

open FStar.UInt8

/// Match on wrapping addition that overflows 8 bits.
/// F*: (200 + 56) mod 256 = 0, so must match 0uy and return 10.
let via_switch_add (a b: UInt8.t) : FStar.UInt32.t =
  match (a +%^ b) with
  | 0uy -> 10ul
  | 1uy -> 20ul
  | _   -> 30ul

/// Match on wrapping subtraction that underflows.
/// F*: (0 - 1) mod 256 = 255, so must match 255uy and return 40.
let via_switch_sub (a b: UInt8.t) : FStar.UInt32.t =
  match (a -%^ b) with
  | 0uy   -> 50ul
  | 255uy -> 40ul
  | _     -> 60ul

/// Match on wrapping multiplication.
/// F*: (128 * 3) mod 256 = 384 mod 256 = 128, so must match 128uy.
let via_switch_mul (a b: UInt8.t) : FStar.UInt32.t =
  match (a *%^ b) with
  | 0uy   -> 70ul
  | 128uy -> 80ul
  | _     -> 90ul

let main () : FStar.Int32.t =
  if via_switch_add 200uy 56uy = 10ul
  && via_switch_sub 0uy 1uy = 40ul
  && via_switch_mul 128uy 3uy = 80ul
  then 0l
  else 1l
