module Substitute

open FStar
open FStar.HyperStack.ST

[@ "substitute" ]
private let test (b: Buffer.buffer Int32.t): Stack unit
  (requires (fun h -> Buffer.live h b /\ Buffer.length b > 0))
  (ensures (fun _ _ _ -> true))
=
  push_frame ();
  Buffer.upd b 0ul 0l;
  pop_frame ();
  ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let b = Buffer.create 1l 1ul in
  test b;
  pop_frame ();
  C.EXIT_SUCCESS
