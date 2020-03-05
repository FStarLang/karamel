module Library

module B = LowStar.Buffer
open LowStar.BufferOps
open FStar.HyperStack.ST

let main (): St Int32.t =
  push_frame ();
  let b = B.alloca_of_list [ 1uy ] in
  let b' = B.alloca_of_list [ 0uy ] in
  MemCpyModel.memcpy b b' 1ul (Ghost.hide 1l);
  let r = b.(0ul) in
  let r = FStar.Int.Cast.uint8_to_int32 r in
  pop_frame ();
  r
