module DepPair

module B = LowStar.Buffer

let non_null_buffer (a: Type) =
  ( x: B.buffer a & squash (not (B.g_is_null x)) )

let deref (x: non_null_buffer Int32.t):
  FStar.HyperStack.ST.Stack Int32.t
    (requires fun h0 -> B.live h0 (dfst x) /\ B.length (dfst x) == 1)
    (ensures fun _ _ _ -> True)
=
  B.index (dfst x) 0ul

let main () =
  let b = B.malloc FStar.HyperStack.root 0l 1ul in
  let b = (| b, () |) in
  deref b
