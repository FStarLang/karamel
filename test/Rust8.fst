module Rust8

open FStar.HyperStack.ST

module B = LowStar.Buffer

let ignore #a (x: a): Stack unit (fun h0 -> True) (fun h0 r h1 -> h0 == h1) = ()

let main_ (): St Int32.t =
  push_frame ();
  let base = B.alloca 0l 12ul in
  let x = B.sub base 0ul 4ul in
  let z = B.sub base 8ul 4ul in
  let z1 = B.sub base 8ul 4ul in
  let x1 = B.sub base 0ul 4ul in
  let y = B.sub base 4ul 4ul in
  let x0 = B.index x 0ul in
  ignore x;
  ignore z;
  ignore z1;
  ignore x1;
  ignore y;
  ignore x0;
  assert (x0 == 0l);
  pop_frame ();
  x0
