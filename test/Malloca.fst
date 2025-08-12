module Malloca

open FStar.HyperStack
open FStar.HyperStack.ST

let f () : UInt32.t = 100ul

let test1 () : Stack unit (fun _ -> False) (fun _ _ _ -> True) =
  let b = FStar.Buffer.create 1uL 999ul in
  ()

let test2 () : Stack unit (fun _ -> False) (fun _ _ _ -> True) =
  let b = FStar.Buffer.create 1uL (f ()) in
  ()

let main () = 0l
