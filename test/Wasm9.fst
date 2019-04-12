module Wasm9

open FStar.HyperStack.ST

module B = LowStar.Buffer

let main (): St Int32.t =
  push_frame ();
  let b = B.alloca 3ul 4ul in
  B.fill (B.offset b 1ul) 0x04ul 2ul;
  let r1 = B.index b 0ul = 3ul in
  let r2 = B.index b 1ul = 4ul in
  let r3 = B.index b 2ul = 4ul in
  let r4 = B.index b 3ul = 3ul in
  pop_frame ();
  if r1 && r2 && r3 && r4 then 0l else 1l
