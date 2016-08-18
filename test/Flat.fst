module Flat

open FStar

type point = {
  x: Int32.t;
  y: Int32.t;
  z: Int32.t;
}

let x p = p.x

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) -> HST.Stl C.int
let main argc argv =
  let p = { x = 0l; y = 1l; z = -1l } in
  let foo = FStar.Int32 (p.x +^ p.y +^ p.z) in
  let bar = x ({ x = 0l; y = 1l; z = -1l }) in
  C.exit_success
