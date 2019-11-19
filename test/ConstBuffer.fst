module ConstBuffer

open FStar.HyperStack.ST

module C = LowStar.ConstBuffer
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack

let cast_and_mutate (x: C.const_buffer U32.t): Stack unit
  (requires fun h0 ->
    C.(qbuf_qual (as_qbuf x) == MUTABLE) /\
    C.live h0 x /\
    C.length x == 1)
  (ensures fun h0 _ h1 ->
    B.modifies C.(loc_buffer x) h0 h1)
=
  let v = C.index x 0ul in
  let x = C.to_buffer x in
  B.upd x 0ul (v `U32.add_mod` 1ul)

let main (): St Int32.t =
  let x = B.malloc HS.root 0ul 1ul in
  cast_and_mutate (C.of_buffer x);
  LowStar.Printf.(printf "new value is: %xul\n" 1ul x done);
  1l
