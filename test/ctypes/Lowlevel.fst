module Lowlevel

(** Dummy types and functions for testing the -ctypes option *)

open FStar.Mul
open FStar.UInt
open FStar.HyperStack.ST

module B = LowStar.Buffer
module M = LowStar.Modifies
module U32 = FStar.UInt32


type point = { x: U32.t; y: U32.t }
type circle = { c: point; r: U32.t }

let square (x: U32.t): U32.t =
  let open U32 in
  x *%^ x

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
type tr = | Rec of U32.t & U32.t & U32.t & U32.t & U32.t
val replicate: n: U32.t -> St tr
let replicate n =
  Rec (n, n, n, n, n)

// Inductives: optimised flat compilation scheme
type int_opt = | IntSome of U32.t | IntNone
val maybe_double: opt: B.pointer int_opt -> Stack unit
  (requires fun h -> B.live h opt /\
     (match FStar.Seq.Base.index (B.as_seq h opt) 0 with
     | IntSome n -> size (2 * U32.v n) U32.n
     | IntNone -> True))
  (requires fun h0 _ h1 -> True)
let maybe_double opt =
  let open U32 in
  let open LowStar.Monotonic.Buffer in
  let v = match B.index opt 0ul with
    | IntSome d -> IntSome (2ul *^ d)
    | IntNone -> IntNone
  in
  upd opt 0ul v

val gen_adder: U32.t -> St (U32.t -> U32.t)
let gen_adder a =
  let open U32 in
  (fun x -> a +%^ x)


// Not supported:

// // Inductives: general compilation scheme
// noeq type eith = | L of U32.t | R of U32.t
// val flip_t: x: eith -> St eith
// let flip_t x =
//   match x with
//   | L n -> R n
//   | R n -> L n

