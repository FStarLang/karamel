module OpEq

let compare' (#a:eqtype)
  (eq:(a -> a -> Tot bool) { eq == op_Equality #a })
  (a1 a2:a):
  bool
=
  a1 `eq` a1

inline_for_extraction noextract
let compare (#a:eqtype) (a1 a2: a): bool =
  compare' (op_Equality #a) a1 a2

let example (x y: UInt32.t) =
  x `compare` y

let main () =
  if example 0ul 0ul then
    0l
  else
    1l
