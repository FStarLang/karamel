module Wasm8

module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32

private
let b: (b:IB.ibuffer UInt32.t { IB.recallable b /\ IB.length b = 4 }) =
  IB.igcmalloc_of_list FStar.HyperStack.root
    [ 0x00102030ul; 0x40506070ul; 0x8090a0b0ul; 0xc0d0e0f0ul ]

let main () =
  IB.recall b;
  let v = IB.index b 3ul in
  let v' = IB.index b 2ul in
  TestLib.checku32 v' 0x8090a0b0ul;
  if v `U32.logand` 0xfful = 0xf0ul && v' = 0x8090a0b0ul then
    0l
  else
    1l
