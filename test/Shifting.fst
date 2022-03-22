module Shifting

open FStar.Ghost

assume
val callback (#erased_x:erased bool) (concrete_y:bool) (#erased_z:erased bool) (concrete_a:bool) : bool

let test (#erased_x:erased bool) (concrete_y:bool) (#erased_z:erased bool) (concrete_a:bool) = concrete_y && concrete_a

let main () = if test #true true #true true then 0l else 1l
