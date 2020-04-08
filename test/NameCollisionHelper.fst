module NameCollisionHelper

type id = { x: Int32.t; y: Int32.t }

inline_for_extraction noextract
let mk (id: Int32.t) =
  { x = id; y = 0l }

