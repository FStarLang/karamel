module Wasm5

open LowStar.BufferOps

module B = LowStar.Buffer

private
let x:(x:B.buffer UInt8.t { B.recallable x /\ B.length x = 3 }) = B.gcmalloc_of_list FStar.HyperStack.root [ 0uy; 1uy; 42uy ]
private
let y:(x:B.buffer UInt8.t { B.recallable x /\ B.length x = 3 }) = B.gcmalloc_of_list FStar.HyperStack.root [ 16uy; 17uy; 18uy ]
private
let z = C.String.of_literal "\0x57\0x68\0x69\0x73\0x70\0x65\0x72\0x54\0x65\0x78\0x74"

let main (): FStar.HyperStack.ST.St Int32.t =
  B.recall x;
  let x: FStar.UInt8.t = x.(2ul) in
  if FStar.UInt8.(42uy -%^ x) = 0uy then
    0l
  else
    1l
