module Wasm1

open FStar.UInt32
type uint32 = FStar.UInt32.t
type nat = x:uint32{ v x >= 0 }

let rec fact (x: nat): nat =
  if x =^ 0ul then
    1ul
  else
    x *%^ (fact (x -^ 1ul))

let minus (x: nat) (y: nat { x >^ y }) =
  x -^ y
