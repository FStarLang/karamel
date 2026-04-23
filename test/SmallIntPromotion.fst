/// Regression test for karamel issue #694.
/// Tests that UInt8/UInt16 integer promotion correctly masks results
/// before comparisons.
module SmallIntPromotion

open FStar.UInt8

/// Comparison after wrapping arithmetic must mask to 8 bits.
/// Use runtime parameters to prevent constant folding.
let check_add_compare (a b c: UInt8.t) : bool = (a +%^ b) = c
let check_sub_compare (a b c: UInt8.t) : bool = (a -%^ b) = c
let check_add_lt (a b c: UInt8.t) : bool = (a +%^ b) <^ c
let check_shl_compare (a: UInt8.t) (s: FStar.UInt32.t{FStar.UInt32.v s < 8}) (c: UInt8.t) : bool =
  (a <<^ s) = c

/// Comparison in if-condition must also mask.
let check_if_add (a b c: UInt8.t) : FStar.Int32.t =
  if (a +%^ b) = c then 0l else 1l

let main () : FStar.Int32.t =
  if check_add_compare 255uy 2uy 1uy
  && check_sub_compare 0uy 1uy 255uy
  && check_add_lt 200uy 100uy 50uy
  && check_shl_compare 0x80uy 1ul 0uy
  && check_if_add 255uy 2uy 1uy = 0l
  then 0l
  else 1l
