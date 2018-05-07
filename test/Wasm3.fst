module Wasm3

open FStar.HyperStack.ST
open FStar.HyperStack

module U128 = FStar.UInt128

open FStar.Buffer

let main (): Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let test = U128.uint64_to_uint128 51910400566UL in
  let test = U128.shift_left test 64ul in
  let test = U128.add_mod test (U128.uint64_to_uint128 17988357517195233983UL) in
  let test = Buffer.create test 1ul in
  C.Loops.in_place_map test 1ul (fun x -> U128.add_mod x x);
  let test = test.(0ul) in
  let test = U128.uint128_to_uint64 test in
  TestLib.check (test = 17529970960680916350UL);
  pop_frame ();
  C.EXIT_SUCCESS
