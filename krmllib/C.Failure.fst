module C.Failure

open FStar.HyperStack.ST

let whatever (): Stack bool
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> h0 == h1)) =
  true

[@(deprecated "LowStar.Failure.failwith")]
let rec failwith (#a: Type) (s: C.String.t): Stack a
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> h0 == h1)) =
  C.String.print s;
  // Defeat recursion warnings.
  if whatever () then
    C.portable_exit 255l;
  failwith s
