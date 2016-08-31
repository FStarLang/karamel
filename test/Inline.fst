module Inline

open FStar
open FStar.HST
open TestLib

let alloc_and_init ():
  StackInline (Buffer.buffer Int32.t) (fun _ -> true) (fun _ _ _ -> true) =
  Buffer.createL [ 0l; 1l; 2l; 3l ]

let alloc_and_init' ():
  StackInline (Buffer.buffer Int32.t) (fun _ -> true) (fun _ _ _ -> true) =
  Buffer.createL [ 4l; 5l; 6l; 7l ]

val main: Int32.t -> Buffer.buffer (Buffer.buffer C.char) ->
  Stack C.int (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let buf = alloc_and_init () in
  let buf': Buffer.buffer Int32.t = alloc_and_init' () in
  check (Buffer.index buf 2ul) 2l;
  pop_frame ();
  C.exit_success
