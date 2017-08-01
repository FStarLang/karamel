module WasmTrap

open FStar.HyperStack
open FStar.HyperStack.ST

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  let b = Buffer.create 0ul 0ul in
  0l
