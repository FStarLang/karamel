module HoistVlaNoWarn

open FStar.HyperStack.ST
open FStar.UInt32
open LowStar.BufferOps

module B = LowStar.Buffer

(* Test: VLA (non-constant size array) that is already at the top of the
   function body (no real statements before it), so it does NOT need to be
   hoisted past statements, and thus does NOT trigger the warning.

   This test should compile successfully both with and without -fhoist-locals. *)

let test_vla_at_top (n: UInt32.t { v n > 0 /\ v n <= 1024 }): St unit =
  push_frame ();
  let buf = B.alloca 0ul n in
  buf.(0ul) <- 42ul;
  TestLib.checku32 buf.(0ul) 42ul;
  pop_frame ()

(* VLA declared at the top, with only other declarations before it. *)
let test_vla_after_decl (n: UInt32.t { v n > 0 /\ v n <= 1024 }): St unit =
  push_frame ();
  let x = 7ul in
  let buf = B.alloca x n in
  TestLib.checku32 buf.(0ul) 7ul;
  pop_frame ()

val main: FStar.Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  St C.exit_code
let main argc argv =
  push_frame ();
  test_vla_at_top 3ul;
  test_vla_after_decl 2ul;
  pop_frame ();
  C.EXIT_SUCCESS
