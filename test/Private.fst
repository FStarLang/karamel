module Private
open FStar.ST

assume val does_not_exist: unit -> unit

private let test () =
  does_not_exist ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  ST.Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  pop_frame ();
  C.exit_success
