module Attributes

open FStar
open FStar.HyperStack
open FStar.HyperStack.ST

[@ "c_inline" ]
let square (x: Int32.t): Tot Int32.t =
  FStar.Int32.(x *^ x)

[@ "substitute" ]
let double (x: Int32.t): Tot Int32.t =
  FStar.Int32.(x +^ x)

val main: unit ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main () =
  push_frame ();
  let open FStar.Int32 in
  let x = square 0l +^ double 0l in
  pop_frame ();
  x
