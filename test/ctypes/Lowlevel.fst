module Lowlevel

(** Dummy types and functions for testing the -ctypes option *)

open FStar.HyperStack.ST

module B = LowStar.Buffer
module M = LowStar.Modifies
module U32 = FStar.UInt32

type point = { x: UInt32.t; y: UInt32.t }
type circle = { c: point; r: UInt32.t}

let square (x: UInt32.t): UInt32.t =
  let open FStar.UInt32 in
  x *%^ x

val point_sum: p1: point -> p2: point -> Stack point
  (requires fun h ->
    U32.v p1.x + U32.v p2.x < 32 /\
    U32.v p1.y + U32.v p2.y < 32)
  (ensures fun h0 _ h1 -> True)
let point_sum p1 p2 =
  let open FStar.UInt32 in
  { x = p1.x +^ p2.x;
    y = p1.y +^ p2.y}

val move_circle: cir: circle -> d: point -> Stack circle
  (requires fun h ->
    U32.v cir.c.x + U32.v d.x < 32 /\
    U32.v cir.c.y + U32.v d.y < 32)
  (requires fun h0 _ h1 -> True)
let move_circle cir d =
  let open FStar.UInt32 in
  { cir with c = point_sum cir.c d }
