module Rust7

module U32 = FStar.UInt32
module B = LowStar.Buffer

open FStar.HyperStack.ST

val add_carry_u32:
  x:U32.t
  -> y:U32.t
  -> r:B.lbuffer U32.t 1 ->
  Stack U32.t
  (requires fun h -> B.live h r)
  (ensures  fun h0 c h1 -> True)
    // modifies1 r h0 h1 /\ v c <= 1 /\
    // (let r = Seq.index (as_seq h1 r) 0 in
    // v r + v c * pow2 (bits t) == v x + v y + v cin))

let add_carry_u32 x y r =
  let res = U32.add_mod x y in
  // let c = (U32.shift_right res 32ul) in
  B.upd r 0ul res;
  0ul
