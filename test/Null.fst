module Null

module B = LowStar.Buffer
open LowStar.BufferOps

open FStar.HyperStack.ST

let f (x: B.pointer_or_null Int32.t): Stack Int32.t
  (requires (fun h -> B.live h x))
  (ensures (fun _ _ _ -> true)) =
  if B.is_null x then
    0l
  else
    !*x

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  f (B.null #Int32.t)
