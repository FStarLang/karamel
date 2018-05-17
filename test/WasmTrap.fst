module WasmTrap

open FStar.HyperStack
open FStar.HyperStack.ST

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let b = Buffer.create 0ul 0ul in
  pop_frame ();
  0l
