module Rustpair

let foo (x: 'a & 'b) : Dv 'a =
  match x with
  | a, _ -> a

let bar (x: 'a & 'b) : Dv 'b =
  match x with
  | _, b -> b

let baz (x: 'a & 'b) : Dv bool =
  match x with
  | _, _ -> true

let main_ () =
  let _ = foo (4ul, true) in
  let _ = bar (false, 4ul) in
  let _ = baz (false, 4ul) in
  0ul
