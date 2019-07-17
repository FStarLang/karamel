module Undefined

module B = LowStar.Buffer

open FStar.HyperStack.ST
open LowStar.BufferOps

let blit (dst src: B.buffer UInt8.t) (len: UInt32.t): Stack bool
  (requires (fun h0 ->
    B.live h0 dst /\ B.live h0 src /\
    B.length dst = 0 /\ B.length src = 0 /\
    B.disjoint dst src /\
    UInt32.v len = 0))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer dst) h0 h1)))
=
  B.blit src 0ul dst 0ul len;
  B.is_null dst

let main (): St Int32.t =
  push_frame ();
  let r = if blit B.null B.null 0ul then 0l else 1l in
  pop_frame ();
  r
