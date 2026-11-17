module HoistVlaWarn

open FStar.HyperStack.ST
open FStar.UInt32
open LowStar.Printf
open LowStar.BufferOps

module B = LowStar.Buffer

(* Test: VLA (non-constant size array) declared AFTER a real statement.
   With -fhoist-locals, this should trigger warning 29 (HoistLocalsVla) because
   the VLA declaration cannot be hoisted past the printf statement.

   This test is compiled with -warn-error -29 to make the warning non-fatal,
   so we can verify the behavior is still correct. *)

let test_vla_after_stmt (n: UInt32.t { v n > 0 /\ v n <= 1024 }): St unit =
  push_frame ();
  let x = 5ul in
  printf "before vla: x=%ul\n" x done;
  let buf = B.alloca 0ul n in
  buf.(0ul) <- x;
  TestLib.checku32 buf.(0ul) x;
  pop_frame ()

val main: FStar.Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  St C.exit_code
let main argc argv =
  push_frame ();
  test_vla_after_stmt 2ul;
  pop_frame ();
  C.EXIT_SUCCESS
