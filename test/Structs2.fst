module Structs2

open FStar.ST

type color = { r: UInt8.t; g: UInt8.t; b: UInt8.t }
type point = { x: UInt32.t; y: UInt32.t; z: UInt32.t }

type t = {
  color: color;
  point: point
}

let test1 (x: t): Stack color (fun _ -> true) (fun _ _ _ -> true) =
  x.color

let touch8 (x: UInt8.t): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x: t = {
    color = { r = 0uy; g = 1uy; b = 2uy };
    point = { x = 3ul; y = 4ul; z = 5ul }
  } in
  let c = test1 x in
  touch8 c.r;
  touch8 x.color.r;
  touch8 x.color.g;
  C.exit_success
