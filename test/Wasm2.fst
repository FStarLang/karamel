module Wasm2

open FStar.HyperStack.ST
open FStar.HyperStack

module U128 = FStar.UInt128

open FStar.Buffer

let main (): Stack FStar.Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let zero = U128.mul_wide 0UL 0UL in
  let b = Buffer.create zero 1ul in
  b.(0ul) <- zero;
  pop_frame ();
  C.exit_success

