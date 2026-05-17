module Assoc

open FStar.Int32

let small_t = x:t{-100 < v x /\ v x < 100}

let test_r (x y z : small_t) : t =
  x +^ (y +^ z)

let test_r' (x y z : small_t) : t =
  x +^ (y -^ z)

let test_l (x y z : small_t) : t =
  (x +^ y) +^ z

let test_l' (x y z : small_t) : t =
  (x +^ y) -^ z

let test4 (x y z w : small_t) : t =
  (x +^ y) -^ (z +^ w)

let test4' (x y z w : small_t) : t =
  (x -^ y) +^ (z -^ w)
