module Shift

open FStar.HyperStack.All
open FStar.UInt8

inline_for_extraction
let f #a (x: a): Stack a (requires fun _ -> True) (ensures fun h0 x' h1 -> h0 == h1 /\ x == x') = x

val main: unit -> St C.exit_code
let main _ =
  let z = (f 0uy -%^ f 1uy) >>^ f 7ul in
  match z with
  | 1uy -> C.EXIT_SUCCESS
