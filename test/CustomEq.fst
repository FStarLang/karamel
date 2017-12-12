module CustomEq

open FStar.HyperStack.ST

type point = {
  x: Int32.t;
  y: Int32.t
}

let f (): Stack nat (fun _ -> true) (fun _ _ _ -> true) =
  2

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  if { x = 0l; y = 1l } = { x = 0l; y = f () } then
    1l
  else if { x = 0l; y = 1l } <> { x = 0l; y = f () } then
    0l
  else
    2l
