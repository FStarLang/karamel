module Null

module B = FStar.Buffer

open FStar.HyperStack.ST
open C.Nullity

let f (x: pointer_or_null Int32.t): Stack Int32.t
  (requires (fun h -> B.live h x))
  (ensures (fun _ _ _ -> true)) =
  if is_null x then
    0l
  else
    !*x

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  f (null Int32.t)
