module Renaming

open FStar.HST

assume val touch: Int32.t -> STL unit (requires (fun _ ->  True)) (ensures (fun _ _ _ -> True))

let f (msg: unit) =
  push_frame ();
  let x = 1l in
  let y = 2l in
  let h = HST.get () in
  let msg = 3l in
  touch msg;
  pop_frame ()
