module StaticHeaderLib

[@@ CInline ]
let private_helper (): FStar.HyperStack.ST.Stack Int32.t
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
=
  0l

inline_for_extraction noextract
val helper: unit -> FStar.HyperStack.ST.Stack Int32.t
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
