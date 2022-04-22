module FunctionalUpdate

module B = LowStar.Buffer
open LowStar.BufferOps
open FStar.HyperStack.ST

type point = { x: Int32.t; y: Int32.t }

let f (p: B.buffer point): Stack unit
  (requires (fun h -> B.live h p /\ B.length p = 1))
  (ensures (fun _ _ _ -> True))
=
  let open LowStar.BufferOps in
  p.(0ul) <- ({ p.(0ul) with x = 0l })

let main (): St Int32.t =
  push_frame ();
  let r = B.alloca ({ x = 1l; y = 2l }) 1ul in
  f r;
  let ret = (!*r).x in
  pop_frame ();
  ret
