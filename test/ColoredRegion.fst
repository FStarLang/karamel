module ColoredRegion

open FStar.HyperStack.ST
open FStar.UInt32
module B = LowStar.Buffer
module HS = FStar.HyperStack
open LowStar.Monotonic.Buffer

let foo (x: UInt32.t) : ST (B.pointer UInt32.t)
(requires (fun _ -> True))
(ensures  (fun _ _ _ -> True))
  = let r = new_colored_region HS.root (-(UInt32.v x)) in
      B.malloc r x 1ul

let main () = 0l
