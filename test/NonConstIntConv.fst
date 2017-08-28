module Test

open FStar.HyperStack.ST

module U32 = FStar.UInt32

assume val n : FStar.UInt.uint_t 32

let main : unit -> ST UInt32.t (fun _ -> True) (fun _ _ _ -> True) =
  fun () -> let x = U32.uint_to_t n in x
