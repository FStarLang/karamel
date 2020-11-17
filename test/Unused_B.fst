module Unused_B

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

let root (x: U32.t) (b: B.buffer U32.t) : HST.St bool =
  Unused_A.caller x b

let main (): HST.St Int32.t =
  let b = B.malloc FStar.HyperStack.root 1ul 1ul in
  if root 5ul b then
    0l
  else
    1l
