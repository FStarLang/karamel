module Base
open FStar.HyperStack.ST

module G = FStar.Ghost
module U32 = FStar.UInt32
module C = C

noeq type slice (t: Type0) : Type0 = { len: U32.t ; ptr: ref t }

inline_for_extraction
noeq
type cbor_string = {
  cbor_string_type: U32.t;
  cbor_string_size: U32.t;
  cbor_string_ptr: slice U32.t;
  cbor_string_perm: Ghost.erased bool;
}
