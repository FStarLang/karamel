/// Regression test for karamel issue #690.
/// Tests that UInt8 bitwise NOT masks upper bits before division
/// and comparison.
module SmallIntBNot

open FStar.UInt8

/// Bitwise NOT must mask before division.
/// ~0x00 = 0xFF = 255, 255 / 2 = 127.
/// Without mask: ~(uint32)0 = 0xFFFFFFFF, 0xFFFFFFFF / 2 = 2147483647,
/// (uint8_t)2147483647 = 255 (WRONG).
let check_not_div (a b: UInt8.t{UInt8.v b > 0}) : UInt8.t = (lognot a) /^ b

/// Bitwise NOT must mask before comparison.
let check_not_compare (a c: UInt8.t) : bool = (lognot a) = c

let main () : FStar.Int32.t =
  if check_not_div 0x00uy 2uy = 127uy
  && check_not_div 0x0Fuy 2uy = 120uy
  && check_not_compare 0x0Fuy 0xF0uy
  && check_not_compare 0xFFuy 0x00uy
  then 0l
  else 1l
