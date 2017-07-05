module Mutable

//
open FStar.Int32
open FStar.HyperStack.ST
open TestLib

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let open FStar.Int32 in
  let mutable x = 1l in
  x <- x +^ x;
  check x 2l;
  pop_frame ();
  C.exit_success
