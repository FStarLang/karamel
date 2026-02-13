module Derived
open FStar.HyperStack.ST

module U32 = FStar.UInt32

let g (c: Base.cbor_string) : Base.cbor_string =
  Base.f (FStar.Ghost.hide true) c

let main_ () = 0ul
