/// Regression test: ETernary wrapping UInt8 arithmetic hides
/// non-atomic expression from mk_arith, causing missing mask.
/// The ternary is marked "atomic" by the catch-all in mk_arith,
/// so consumers (switch, comparisons) skip the mask.
module SmallIntTernary

open FStar.UInt8

/// Switch on a ternary whose "then" branch is wrapping addition.
/// F*: flag=true, a=200, b=56 => (200+56) mod 256 = 0, match 0uy => 10.
let switch_on_ternary (flag: bool) (a b: UInt8.t) : FStar.UInt32.t =
  match (if flag then (a +%^ b) else 0uy) with
  | 0uy -> 10ul
  | 1uy -> 20ul
  | _   -> 30ul

/// Comparison on a ternary whose "then" branch is wrapping addition.
/// F*: flag=true, a=200, b=56 => (200+56) mod 256 = 0 = 0uy => true.
let cmp_on_ternary (flag: bool) (a b: UInt8.t) : bool =
  (if flag then (a +%^ b) else 1uy) = 0uy

/// BNot inside ternary, feeding a switch.
/// F*: flag=true, x=0x0Fuy => lognot 0x0F = 0xF0 = 240, match 240uy => 99.
let switch_ternary_bnot (flag: bool) (x: UInt8.t) : FStar.UInt32.t =
  match (if flag then (UInt8.lognot x) else 0uy) with
  | 0uy   -> 77ul
  | 240uy -> 99ul
  | _     -> 88ul

/// Nested ternary: both branches are arithmetic.
/// F*: f1=true, f2=false, a=200, b=56, c=100, d=200 =>
///     inner = (100+200) mod 256 = 44. match 44uy => 55.
let switch_nested_ternary (f1 f2: bool) (a b c d: UInt8.t) : FStar.UInt32.t =
  match (if f1 then (if f2 then (a +%^ b) else (c +%^ d)) else 0uy) with
  | 0uy  -> 33ul
  | 44uy -> 55ul
  | _    -> 66ul

let main () : FStar.Int32.t =
  if switch_on_ternary true 200uy 56uy = 10ul
  && cmp_on_ternary true 200uy 56uy = true
  && switch_ternary_bnot true 0x0Fuy = 99ul
  && switch_nested_ternary true false 200uy 56uy 100uy 200uy = 55ul
  then 0l
  else 1l
