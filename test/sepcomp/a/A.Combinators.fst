module A.Combinators
include A.Base
module U32 = FStar.UInt32

inline_for_extraction
let f
  #a
  (g: (U32.t -> Tot a))
  (x: t)
: Tot a
=
  if a_le_b x
  then g (x.b `U32.sub` x.a)
  else g (x.a `U32.sub` x.b)
