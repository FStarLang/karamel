module Wasm1

open FStar.ST
open FStar.UInt32

type uint32 = FStar.UInt32.t

let rec fact (x: uint32): Stack uint32 (fun _ -> true) (fun _ _ _ -> true) =
  if x =^ 0ul then
    1ul
  else
    x *%^ (fact (x -^ 1ul))

let maybe_true (): Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

let fact' (x: uint32): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  let _ = if maybe_true () then fact 5ul else fact x in
  ()

let minus (x: uint32) (y: uint32 { x >^ y }) =
  x -^ y
