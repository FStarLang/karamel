module Rust6

open FStar.HyperStack.ST

module B = LowStar.Buffer
module C = LowStar.ConstBuffer


inline_for_extraction noextract
val sub_len:
  b: C.const_buffer UInt32.t ->
  Stack (C.const_buffer UInt32.t)
  (requires fun h -> C.live h b /\ C.length b == 2)
  (ensures  fun h0 r h1 -> h0 == h1 /\ C.live h1 r /\
    C.length r == 2 /\
    B.loc_includes (C.loc_buffer b) (C.loc_buffer r))

let sub_len b =
  C.sub b 0ul 2ul

inline_for_extraction noextract
val copy:
  #a: Type
  -> len:UInt32.t
  -> o:B.buffer a
  -> i:C.const_buffer a ->
  Stack unit
    (requires fun h0 -> B.live h0 o /\ C.live h0 i /\
      B.length o == UInt32.v len /\ C.length i == UInt32.v len /\
      B.disjoint (C.cast i) o)
    (ensures  fun h0 _ h1 -> True)

let copy #a len o i = LowStar.BufferOps.blit (C.cast i) 0ul o 0ul len

let f (b: C.const_buffer UInt32.t) : ST unit
  (requires fun h -> C.live h b /\ C.length b == 2)
  (ensures fun _ _ _ -> True)
  =
  push_frame ();
  let res = B.alloca 0ul 2ul in
  copy 2ul res (sub_len b);
  pop_frame()

let main_ () : St Int32.t =
  0l
