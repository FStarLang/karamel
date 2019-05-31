module Explode

open FStar.HyperStack.ST

type point = | Point: x:UInt32.t -> y:UInt32.t -> point

type vector = | Vector: base:point -> dir:point -> vector

let foo (vec: vector): St UInt32.t =
  vec.base.x `UInt32.add_mod` vec.base.y `UInt32.add_mod` vec.dir.x `UInt32.add_mod` vec.dir.y

let main (): St Int32.t =
  let v = Vector (Point 0ul 1ul) (Point 2ul 3ul) in
  if foo v = 6ul then
    0l
  else
    1l
