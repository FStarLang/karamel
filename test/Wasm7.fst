module Wasm7

open FStar.HyperStack.ST

type t2 =
| A: UInt32.t -> UInt32.t -> t2
| B: UInt32.t -> UInt32.t -> UInt32.t -> t2

let v2 (): St t2 =
  B 0ul 1ul 2ul

let main () =
  match v2 () with
  | B 0ul 1ul 2ul -> 0l
  | _ -> 2l
