module Rustnegliteral

module I8 = FStar.Int8
module I32 = FStar.Int32
module I64 = FStar.Int64

(* Rust has no negative literals: `-1i64` is unary minus applied to `1i64`,
   and method calls bind tighter than unary minus. A negative literal used
   as the receiver of a wrapping arithmetic method must therefore be printed
   as `(-1i64).wrapping_sub(x)`; printed bare, `-1i64.wrapping_sub(x)` means
   `-(1i64.wrapping_sub(x))`, that is `x - 1`. *)

let neg_one_minus (x: I64.t) : I64.t =
  I64.sub (-1L) x

let int32_min_plus (x: I32.t { 0 <= I32.v x }) : I32.t =
  I32.add (-2147483648l) x

let int8_min_minus (x: I8.t { I8.v x <= 0 }) : I8.t =
  I8.sub (-128y) x

let main_ () : HyperStack.ST.St I32.t =
  if neg_one_minus 4L = (-5L) &&
     neg_one_minus (-5L) = 4L &&
     int32_min_plus 1l = (-2147483647l) &&
     int8_min_minus (-1y) = (-127y)
  then 0l
  else 1l
