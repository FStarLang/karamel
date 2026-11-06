module SizeofShadow

(* Locals named after C types that KaRaMeL prints by itself must be renamed.
   Otherwise, `sizeof (uint64_t)` in the `memcpy` of a blit refers to the
   `uint32_t` parameter, and only half of the data gets copied. *)

open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8

let copy64 (dst src: B.buffer U64.t) (uint64_t: U32.t) :
  Stack unit
    (requires fun h -> B.live h dst /\ B.live h src /\ B.disjoint dst src /\
                       B.length dst == U32.v uint64_t /\ B.length src == U32.v uint64_t)
    (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer dst) h0 h1 /\
                            FStar.Seq.equal (B.as_seq h1 dst) (B.as_seq h0 src))
= B.blit src 0ul dst 0ul uint64_t

(* The other direction: `sizeof (uint8_t)` would become 4 and overflow. *)
let copy8 (dst src: B.buffer U8.t) (n: U32.t) :
  Stack unit
    (requires fun h -> B.live h dst /\ B.live h src /\ B.disjoint dst src /\
                       B.length dst == U32.v n /\ B.length src == U32.v n)
    (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer dst) h0 h1 /\
                            FStar.Seq.equal (B.as_seq h1 dst) (B.as_seq h0 src))
= let uint8_t = n in
  B.blit src 0ul dst 0ul uint8_t

let main () : St C.exit_code =
  push_frame ();
  let src = B.alloca 7uL 4ul in
  let dst = B.alloca 0uL 4ul in
  copy64 dst src 4ul;
  let last = B.index dst 3ul in
  let src8 = B.alloca 9uy 4ul in
  let dst8 = B.alloca 0uy 4ul in
  copy8 dst8 src8 4ul;
  let last8 = B.index dst8 3ul in
  pop_frame ();
  if last = 7uL && last8 = 9uy then C.EXIT_SUCCESS else C.EXIT_FAILURE
