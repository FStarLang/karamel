module Caller
open FStar.HyperStack.ST

module U32 = FStar.UInt32

let h (c: Base.cbor_string) : U32.t =
  Derived.g c

let main_ () : St Int32.t = 0l
