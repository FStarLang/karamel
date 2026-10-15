module Issue756

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

let direct_lt (a: U64.t) (b: U32.t) : bool =
  U32.lt (Cast.uint64_to_uint32 a) b

let direct_eq (a: U64.t) (b: U32.t) : bool =
  (Cast.uint64_to_uint32 a) = b

// Same, but with a32 bound locally.

let local_lt (a: U64.t) (b: U32.t) : bool =
  let a32 = Cast.uint64_to_uint32 a in
  U32.lt a32 b

let local_eq (a: U64.t) (b: U32.t) : bool =
  let a32 = Cast.uint64_to_uint32 a in
  a32 = b
