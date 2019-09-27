module A

open FStar.Mul
open FStar.UInt
open FStar.HyperStack.ST

module M = LowStar.Modifies
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open B
open D

let c = 6ul
let p = { x = 8ul; y = 13ul }

val point_sum: p1: point -> p2: point -> Stack point
  (requires fun h ->
    size (U32.v p1.x + U32.v p2.x) U32.n /\
    size (U32.v p1.y + U32.v p2.y) U32.n)
  (ensures fun h0 _ h1 -> True)
let point_sum p1 p2 =
  let open FStar.UInt32 in
  { x = p1.x +^ p2.x;
    y = p1.y +^ p2.y}

val move_circle: cir: circle -> d: point -> Stack circle
  (requires fun h ->
    size (U32.v cir.c.x + U32.v d.x) U32.n /\
    size (U32.v cir.c.y + U32.v d.y) U32.n)
  (requires fun h0 _ h1 -> True)
let move_circle cir d =
  let open FStar.UInt32 in
  { cir with c = point_sum cir.c d }

