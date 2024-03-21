module Rust7

open FStar.HyperStack.ST

module B = LowStar.Buffer

let ignore #a (x: a): Stack unit (fun h0 -> True) (fun h0 r h1 -> h0 == h1) = ()

let main_ (): St Int32.t =
  push_frame ();
  let base = B.alloca 0l 12ul in
  let x = B.sub base 0ul 4ul in
  let x1 = B.sub base 0ul 4ul in
  ignore x1;
  let x0 = B.index x 0ul in
  assert (x0 == 0l);
  pop_frame ();
  x0
