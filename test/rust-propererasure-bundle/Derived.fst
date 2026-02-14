module Derived
open FStar.HyperStack.ST

module U32 = FStar.UInt32

let g (c: Base.cbor_string) : U32.t =
  c.Base.cbor_string_type
