module Rustfn4
module B = LowStar.Buffer
open FStar.HyperStack.ST

inline_for_extraction
type t =
  r:B.lbuffer bool 1 ->
  Stack (B.lbuffer bool 1)
    (requires fun h0 -> B.live h0 r)
    (ensures fun _ _ _ -> True)

noeq type s = {
  r: B.lbuffer bool 1;
  f: t;
}

let f : t = fun r ->
  B.upd r 0ul true;
  r

let g (x: s) :
    Stack unit
      (requires fun h0 -> B.live h0 x.r)
      (ensures fun _ _ _ -> True) =
  let _ = x.f x.r in ()

let h (x: s) =
  push_frame ();
  let ptr = B.alloca false 1ul in
  g { x with r = ptr };
  pop_frame ()

let i () =
  push_frame ();
  let ptr = B.alloca false 1ul in
  let x = { r = ptr; f } in
  h x;
  pop_frame ()

let main_ () =
  i (); 0ul