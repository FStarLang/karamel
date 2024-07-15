module Rust7

module U32 = FStar.UInt32
module B = LowStar.Buffer
open LowStar.BufferOps

open FStar
open FStar.HyperStack.ST

val add_carry_u32:
  x:U32.t
  -> y:U32.t
  -> r:B.lbuffer U32.t 1
  -> p:B.lbuffer U32.t 1 ->
  Stack U32.t
  (requires fun h -> B.live h r /\ B.live h p)
  (ensures  fun h0 c h1 -> True)
    // modifies1 r h0 h1 /\ v c <= 1 /\
    // (let r = Seq.index (as_seq h1 r) 0 in
    // v r + v c * pow2 (bits t) == v x + v y + v cin))

let add_carry_u32 x y r p =
  let z = B.index p 0ul in
  let res = U32.add_mod x y in
  let res = U32.add_mod res z in
  // let c = (U32.shift_right res 32ul) in
  B.upd r 0ul res;
  0ul

let test_alloca (x: UInt32.t)  : Stack UInt32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True)) =
  push_frame();
  let ptr = B.alloca 0ul 10ul in
  B.upd ptr 0ul x;
  let res = B.index ptr 0ul in
  pop_frame();
  x

// simple for loop example - note that there is no framing
let loop (ptr:B.lbuffer U32.t 10)  : Stack UInt32.t
  (requires (fun h0 -> B.live h0 ptr))
  (ensures (fun h0 r h1 -> True)) =
  push_frame();
  C.Loops.for 0ul 0ul
    (fun h i -> B.live h ptr)
    (fun i -> B.upd ptr i 1ul);
  C.Loops.for 0ul 1ul
    (fun h i -> B.live h ptr)
    (fun i -> B.upd ptr i 1ul);
  C.Loops.for 0ul 10ul
    (fun h i -> B.live h ptr)
    (fun i -> B.upd ptr i 1ul);
  let sum = B.index ptr 0ul in
  pop_frame();
  sum


// let loop_alloc ()  : Stack UInt32.t
//   (requires (fun h0 -> True))
//   (ensures (fun h0 r h1 -> True)) =
//   push_frame();
//   let ptr = B.alloca 0ul 10ul in
//   C.Loops.for 0ul 9ul
//     (fun h i -> B.live h ptr)
//     (fun i -> B.upd ptr i 1ul);
//   let sum = B.index ptr 0ul in
//   pop_frame();
//   sum
