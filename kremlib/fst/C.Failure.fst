module C.Failure

open FStar.HyperStack.ST

// Convenience functions
let rec failwith (#a: Type) (s: C.String.t): Stack a
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> h0 == h1)) =
  C.String.print s;
  C.exit 255l;
  failwith s
