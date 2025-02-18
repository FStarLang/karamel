module Ctypes2

open FStar.Mul
open FStar.UInt
open FStar.HyperStack.ST

module U32 = FStar.UInt32

open Ctypes1

val point_sum2: p1: point -> p2: point -> Stack point
  (requires fun h ->
    size (U32.v p1.x + U32.v p2.x) U32.n /\
    size (U32.v p1.y + U32.v p2.y) U32.n)
  (ensures fun h0 _ h1 -> True)
let point_sum2 p1 p2 =
  let open FStar.UInt32 in
  { x = p1.x +^ p2.x;
    y = p1.y +^ p2.y}

