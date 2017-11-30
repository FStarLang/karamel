module Uu
module Int32 = FStar.Int32

open FStar.Int32
open FStar.HyperStack.ST
open FStar.Buffer

let f (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  1l

let main () =
  push_frame ();
  let x = f () +^ f () in
  let y = 1l +^ f () in
  let b = createL [ -1l; 1l ] in
  let z = b.(0ul) +^ b.(1ul) in
  let t = b.(let r = b.(1ul) in Int.Cast.int32_to_uint32 r) in
  let r = x -^ y +^ z +^ t +^ b.(0ul) in
  pop_frame ();
  r
