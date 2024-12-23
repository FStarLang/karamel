module NameCollision

let mk = NameCollisionHelper.mk

open NameCollisionHelper

let f (): FStar.HyperStack.ST.St Int32.t = 0l

let main () =
  let unsigned = f () in
  (mk unsigned).y
