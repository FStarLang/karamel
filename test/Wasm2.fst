module Wasm2

open FStar.HyperStack.ST
open FStar.HyperStack

module U128 = FStar.UInt128

open LowStar.Buffer
open LowStar.BufferOps

(* Note: using exit_code makes is_EXIT_FAILURE reachable, and we don't know how
 * to compile this discriminator since the Wasm backend has not support for
 * switches yet. *)
let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let test = U128.mul_wide 0x30586768dbe7UL 0x3FFFFFFFFFFF69UL in
  let b = alloca (U128.uint64_to_uint128 0UL) 1ul in
  b.(0ul) <- test;
  LowStar.Ignore.ignore b;
  pop_frame ();
  let low = U128.uint128_to_uint64 test in
  let high = U128.(uint128_to_uint64 (test >>^ 64ul)) in
  TestLib.check (low = 17988357517195233983UL && high = 51910400566UL);
  let test = U128.add_mod test test in
  let test = U128.uint128_to_uint64 test in
  TestLib.check (test = 17529970960680916350UL);
  0l
