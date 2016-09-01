module Renaming

open TestLib
open FStar.HST

val f: Int64.t ->
  Stack unit (fun _ -> true) (fun _ _ _ -> true)
let f msg =
  push_frame ();
  let x = 1l in
  let y = 2l in
  let h = HST.get () in
  let msg = 3l in
  touch msg;
  pop_frame ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  HST.Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  f 0L;
  pop_frame ();
  C.exit_success
