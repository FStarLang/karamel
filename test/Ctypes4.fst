module Ctypes4

open FStar.Mul
open FStar.UInt
open FStar.HyperStack.ST

module B = LowStar.Buffer
module M = LowStar.Modifies
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U128 = FStar.UInt128

open Ctypes1
open Ctypes3

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

let my_not_pointer = my_not

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
  (ensures fun h0 _ h1 -> True)
let maybe_double opt =
  let open U32 in
  let open LowStar.Monotonic.Buffer in
  let v = match B.index opt 0ul with
    | IntSome d -> IntSome (2ul *^ d)
    | IntNone -> IntNone
  in
  upd opt 0ul v

// Inductives: general compilation scheme
noeq type eith = | L of U32.t | R of U16.t
val make_L: x: U32.t -> St eith
let make_L x = L x

val make_R: x: U16.t -> St eith
let make_R x = R x

val flip_t: p: B.pointer eith -> Stack unit
  (requires fun h -> B.live h p)
  (ensures fun h0 _ h1 -> True)
let flip_t p =
  let open U32 in
  let open LowStar.Monotonic.Buffer in
  let v = match B.index p 0ul with
    | L n -> R (FStar.Int.Cast.uint32_to_uint16 n)
    | R n -> L (FStar.Int.Cast.uint16_to_uint32 n)
  in
  upd p 0ul v

type unsupported_t = {
  a1: U32.t;
  b1: U128.t;
}

[@ CAbstractStruct ]
type unsupported_abstract_t = {
  a2: U32.t;
  b2: U128.t;
}

type u = B.pointer unsupported_abstract_t

let create_u (): St u =
  B.malloc FStar.HyperStack.root ({ a2 = 6ul; b2 = Int.Cast.Full.uint64_to_uint128 0UL }) 1ul

val read_u_a2: x: u -> Stack U32.t
  (requires fun h -> B.live h x)
  (ensures fun h0 _ h1 -> True)
let read_u_a2 x =
  let open LowStar.Monotonic.Buffer in
  let v = B.index x 0ul in
  v.a2
