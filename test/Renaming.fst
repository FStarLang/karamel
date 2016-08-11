module Renaming

open TestLib
open FStar.HST

val f: Int64.t -> Stl unit
let f msg =
  push_frame ();
  let x = 1l in
  let y = 2l in
  let h = HST.get () in
  let msg = 3l in
  touch msg;
  pop_frame ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) -> HST.Stl C.int
let main argc argv =
  f 0L;
  C.exit_success
