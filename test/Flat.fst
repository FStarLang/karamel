module Flat

open FStar
open FStar.ST

type point = {
  x: Int32.t;
  y: Int32.t;
  z: Int32.t;
}

let x p = p.x

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  ST.Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let p = { x = 0l; y = 1l; z = -1l } in
  let foo = FStar.Int32.(p.x +^ p.y +^ p.z) in
  let bar = x ({ x = 0l; y = 1l; z = -1l }) in
  pop_frame ();
  C.exit_success
