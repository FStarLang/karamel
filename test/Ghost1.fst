module Ghost1

open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt32

open Ghost2

let test_log (x:UInt32.t) : Stack log (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True)) =
  let log = Ghost.hide x in
  log

let test (u:unit) : Stack unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True)) =
  let l = test_log 1ul in
  let l' = test_log 2ul in
  ()

let main () =
  C.EXIT_SUCCESS
