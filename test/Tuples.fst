module Tuples

open FStar.HyperStack.ST

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let x = 1ul, 2ul in
  let y = x, x in
  let z = 1ul, x, y in
  let a, b = x in
  pop_frame ();
  C.exit_success
