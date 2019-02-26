module Lowlevel

(** Dummy types and functions for testing the -ctypes option *)

open FStar.HyperStack.ST

module B = LowStar.Buffer
module M = LowStar.Modifies
module U32 = FStar.UInt32

type point = { x: U32.t; y: U32.t }
type circle = { c: point; r: U32.t }

let square (x: U32.t): U32.t =

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

// Inductives: enum compilation scheme
type my_bool = | MyTrue | MyFalse
val my_not: b: B.pointer my_bool -> Stack unit
  (requires fun h -> B.live h b)
  (requires fun h0 _ h1 -> True)
let my_not b =
  let open LowStar.Monotonic.Buffer in
  let v = match B.index b 0ul with
    | MyTrue -> MyFalse
    | MyFalse -> MyTrue
  in
  upd b 0ul v;
  ()

// Inductives: record compilation scheme
type tr = | Rec of U32.t * U32.t * U32.t * U32.t * U32.t
val replicate: n: U32.t -> Stack tr
  (requires fun h -> True)
  (requires fun h0 _ h1 -> True)
let replicate n =
  Rec (n, n, n, n, n)


// // Inductives: optimised flat compilation scheme
// type int_opt = | Some of U32.t | None

// // Inductives: general compilation scheme
// assume new type foo
// assume new type bar
// noeq type t_general = | A of foo | B of bar


// val my_not: b: B.pointer U32.t -> Stack unit
//   (requires fun h -> B.live h b)
//   (requires fun h0 _ h1 -> B.live h1 b)
// let my_not b =
//   let open LowStar.Monotonic.Buffer in
//   let v = B.index b 0ul in
//   upd b 0ul 5ul;
//   ()


// val new_buf: last: U32.t -> Stack (FStar.Seq.lseq U32.t 5 )
//   (requires fun h -> True)
//   (requires fun h0 _ h1 -> True)
// let new_buf last =
//   FStar.Seq.createL [1ul; 2ul; 3ul; 4ul; last]


// val list_of_circles: cir: circle -> n: U32.t -> Stack circle
//   (requires fun h ->
//     U32.v cir.c.x + U32.v d.x < 32 /\
//     U32.v cir.c.y + U32.v d.y < 32)
//   (requires fun h0 _ h1 -> True)
// let rec list_of_circles cir n =
  
