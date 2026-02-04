module MutualStruct
open FStar.HyperStack.ST

#set-options "--__no_positivity" // because FStar.HyperStack.ST.ref does not respect positivity

module U64 = FStar.UInt64
module U8 = FStar.UInt8

let main () = C.EXIT_SUCCESS // dummy

// SUCCESS
noeq
type object1_tagged = {
  object1_tagged_tag: U64.t;
  object1_tagged_payload: ref object1;
}
and object1 = {
  object1_type: U8.t;
  object1_payload: object1_tagged;
}

(*
// FAIL to compile: struct types are generated in the wrong order, leading to the compiler complaining about `object2_tagged` being an incomplete type

// The order of mutually recursive type
// definitions should match that of C, in the sense that types that
// depend on other types only behind `ref` should be defined first.
// So the correct order for `object2` below is `object1` above.

noeq
type object2 = {
  object2_type: U8.t;
  object2_payload: object2_tagged;
}
and object2_tagged = {
  object2_tagged_tag: U64.t;
  object2_tagged_payload: ref object2;
}

// FAIL to compile: same here
noeq
type object3 = {
  object3_type: U8.t;
  object3_map: object3_map;
}
and object3_pair = {
  object3_pair_key: object3;
  object3_pair_payload: object3;
}
and object3_map = {
  object3_map_entry_count: U64.t;
  object3_map_payload: ref object3_pair;
}

// The proper order of `object3` above is `object4` below:
*)

noeq
type object4_map = {
  object4_map_entry_count: U64.t;
  object4_map_payload: ref object4_pair;
}
and object4 = {
  object4_type: U8.t;
  object4_map: object4_map;
}
and object4_pair = {
  object4_pair_key: object4;
  object4_pair_payload: object4;
}

(*
// FAIL to compile: incomplete type, this time because the monomorphized type instance for `object6_map (ref object6_pair)` is not generated
noeq
type object6_map ([@@@strictly_positive] param: Type0) = {
  object6_map_entry_count: U64.t;
  object6_map_payload: param;
}
noeq
type object6 = {
  object6_type: U8.t;
  object6_map: object6_map (ref object6_pair);
}
and object6_pair = {
  object6_pair_key: object6;
  object6_pair_payload: object6;
}
*)

// This test extracts and compiles.

noeq
type object7_tagged = {
  object7_tagged_tag: U64.t;
  object7_tagged_payload: ref object7;
}
and object7_map = {
  object7_map_entry_count: U64.t;
  object7_map_payload: ref object7_pair;
}
and object7_case = {
  object7_case_tagged: object7_tagged;
  object7_case_map: object7_map;
}
and object7 = {
  object7_type: U8.t;
  object7_payload: object7_case;
}
and object7_pair = {
  object7_pair_fst: object7;
  object7_pair_snd: object7;
}
