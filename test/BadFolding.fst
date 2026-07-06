module BadFolding

open FStar.UInt32
open FStar.HyperStack.ST

let side_effect_fn : UInt32.t -> UInt32.t -> Stack UInt32.t (requires fun _ -> False) (ensures fun _ _ _ -> True) =
  fun a b -> a +%^ b

let test1 (a b: UInt32.t) : Stack UInt32.t  (requires fun _ -> False) (ensures fun _ _ _ -> True) =
  0ul *%^ side_effect_fn a b

let test2 (a b: UInt32.t) : Stack UInt32.t  (requires fun _ -> False) (ensures fun _ _ _ -> True) =
  side_effect_fn a b *%^ 0ul

let test3 (a b: UInt32.t) : Stack UInt32.t  (requires fun _ -> False) (ensures fun _ _ _ -> True) =
  1ul *%^ side_effect_fn a b

let test4 (a b: UInt32.t) : Stack UInt32.t  (requires fun _ -> False) (ensures fun _ _ _ -> True) =
  0ul %^ side_effect_fn a b

let test5 (a b: UInt32.t) : Stack UInt32.t  (requires fun _ -> False) (ensures fun _ _ _ -> True) =
  side_effect_fn a b %^ 1ul

let main () = 0l
