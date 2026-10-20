module SmallIntMacro
(* Make sure we emit narrowing casts for macros. *)

open FStar.Integers
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module Cast = FStar.Int.Cast

[@CMacro]
private let max8 : U8.t =
  [@@CInline] let zero = 0uy in // prevent F* from reducing this ahead of time
  U8.lognot zero

[@CMacro]
private let max16 : U16.t =
  [@@CInline] let zero = 0us in
  U16.lognot zero

let signed_max8 () : FStar.Int8.t =
  Cast.uint8_to_int8 (U8.shift_right max8 1ul)

let equal8 (x : U8.t) : bool = x = max8
let wide8 () : FStar.UInt32.t = Cast.uint8_to_uint32 max8
let half8 () : U8.t = U8.div max8 2uy

let signed_max16 () : FStar.Int16.t =
  Cast.uint16_to_int16 (U16.shift_right max16 1ul)

let equal16 (x : U16.t) : bool = x = max16
let wide16 () : FStar.UInt32.t = Cast.uint16_to_uint32 max16
let half16 () : U16.t = U16.div max16 2us
