module Rustpropererasure
open FStar.HyperStack.ST

module G = FStar.Ghost
module U32 = FStar.UInt32

noeq type slice (t: Type0) : Type0 = { len: U32.t ; ptr: ref t }

inline_for_extraction
noeq
type cbor_string = {
  cbor_string_type: U32.t;
  cbor_string_size: U32.t;
  cbor_string_ptr: slice U32.t;
  cbor_string_perm: Ghost.erased bool;
}

let cbor_string_reset_perm (p: Ghost.erased bool) (c: cbor_string) : cbor_string = {
  c with cbor_string_perm = p && c.cbor_string_perm
}

let main_ () = 0ul
