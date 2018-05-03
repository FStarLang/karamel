module Wasm4

open FStar.HyperStack.ST

type t = | A | B | C | D

let test (x: t{ x <> D }): St Int32.t =
  match x with
  | B -> 1l
  | C -> 0l
  | _ -> 3l


let main (): St Int32.t =
  test C
