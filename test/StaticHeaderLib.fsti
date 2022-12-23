module StaticHeaderLib

type t = { x: Int32.t; y: Int32.t }

//[@@ CInline ]
let private_helper (): FStar.HyperStack.ST.Stack t
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
=
  { x = 0l; y = 0l }

inline_for_extraction noextract
val helper: unit -> FStar.HyperStack.ST.Stack Int32.t
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
