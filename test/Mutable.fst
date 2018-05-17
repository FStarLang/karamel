module Mutable

//
open FStar.Int32
open FStar.HyperStack.ST
open TestLib

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let open FStar.Int32 in
  let mutable x = 1l in
  x <- x +^ x;
  check32 x 2l;
  pop_frame ();
  C.EXIT_SUCCESS
