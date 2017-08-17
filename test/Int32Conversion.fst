module Int32Conversion

open FStar.Int32
open FStar.HyperStack.ST

open TestLib

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  check32 44l 44l;
  C.exit_success
