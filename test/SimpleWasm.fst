module SimpleWasm
open FStar.HyperStack.ST

val f: unit -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
let f () =
  ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  f ();
  pop_frame ();
  C.EXIT_SUCCESS
