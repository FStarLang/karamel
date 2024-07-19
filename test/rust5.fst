module Rust5

open FStar.HyperStack.ST

module B = LowStar.Buffer

let ignore #a (x: a): Stack unit (fun h0 -> True) (fun h0 r h1 -> h0 == h1) = ()


let main_ (): St Int32.t =
  push_frame ();
  let base = B.alloca 0l 2ul in
  let x = B.sub base 0ul 1ul in
  let x0 = B.index x 0ul in
  assert (x0 == 0l);
  ignore base;
  let y = B.sub base 0ul 2ul in
  let y0 = B.index y 1ul in
  assert (y0 == 0l);
  pop_frame ();
  FStar.Int32.add x0 y0
