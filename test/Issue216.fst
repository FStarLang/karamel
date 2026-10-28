module Issue216

open FStar.UInt32

(* a remains live after the nested binding of d. *)
let test (x: UInt32.t): UInt32.t =
  let a = x +%^ 1ul in
  let c =
    if a >^ 0ul then
      let d = a +%^ 1ul in
      d +%^ d
    else
      0ul
  in
  a +%^ c

let main () =
  if test 0ul = 5ul then 0l else 1l
