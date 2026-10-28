module Issue216TailCalls

open FStar.UInt32

(* Tail-call compilation makes a a mutable local, exposing it to merging. *)
let rec test2 (a: UInt32.t{v a < 10}): Tot UInt32.t (decreases v a) =
  let c =
    let g = 10ul +^ a in
    if g >^ 5ul then
      let d = g -^ 1ul in
      g +^ d
    else
      0ul
  in
  if a >^ 0ul then
    test2 (a -^ 1ul)
  else
    c

let main () =
  if test2 0ul = 19ul && test2 9ul = 19ul then 0l else 1l
