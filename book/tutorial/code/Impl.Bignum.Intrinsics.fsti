/// Linking with the outside world
/// ==============================

module Impl.Bignum.Intrinsics

/// This module just demonstrates how to expose a C-written function in F*. We
/// don't currently use this module anywhere but it's one of the suggested
/// exercises.

module B = LowStar.Buffer

open FStar.HyperStack.ST

val add_carry (dst: B.buffer UInt32.t) (x y: UInt32.t) (c: UInt32.t): Stack UInt32.t
  (requires fun h0 ->
    B.live h0 dst /\
    B.length dst == 1)
  (ensures fun h0 c1 h1 ->
    B.(modifies (loc_buffer dst) h0 h1) /\ (
    let r = UInt32.v x + UInt32.v y + UInt32.v c in
    UInt32.v (B.get h1 dst 0) == r % pow2 32 /\
    UInt32.v c1 == r / pow2 32))

