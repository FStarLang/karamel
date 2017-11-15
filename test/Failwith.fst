module Failwith

open FStar.HyperStack.ST
open C.String

let a_bool (): Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  if a_bool () then
    0l
  else
    C.Failure.failwith !$"unexpected"
