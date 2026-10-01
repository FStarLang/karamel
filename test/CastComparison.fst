/// Regression test for #756: comparisons must preserve narrowing casts.
module CastComparison

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

/// Direct casts and casts bound to locals must agree for every comparison,
/// with the cast on either side. Parameters keep these checks at runtime.
let check_u32 (a: U64.t) (b: U32.t) : bool =
  let a32 = Cast.uint64_to_uint32 a in
  ((Cast.uint64_to_uint32 a = b) = (a32 = b))
  && ((Cast.uint64_to_uint32 a <> b) = (a32 <> b))
  && (U32.lt (Cast.uint64_to_uint32 a) b = U32.lt a32 b)
  && (U32.lte (Cast.uint64_to_uint32 a) b = U32.lte a32 b)
  && (U32.gt (Cast.uint64_to_uint32 a) b = U32.gt a32 b)
  && (U32.gte (Cast.uint64_to_uint32 a) b = U32.gte a32 b)
  && ((b = Cast.uint64_to_uint32 a) = (b = a32))
  && ((b <> Cast.uint64_to_uint32 a) = (b <> a32))
  && (U32.lt b (Cast.uint64_to_uint32 a) = U32.lt b a32)
  && (U32.lte b (Cast.uint64_to_uint32 a) = U32.lte b a32)
  && (U32.gt b (Cast.uint64_to_uint32 a) = U32.gt b a32)
  && (U32.gte b (Cast.uint64_to_uint32 a) = U32.gte b a32)

/// Removing generated UInt32 upcasts must retain the inner narrowing casts.
let check_u16 (a: U64.t) (b: U16.t) : bool =
  let a16 = Cast.uint64_to_uint16 a in
  ((Cast.uint64_to_uint16 a = b) = (a16 = b))
  && (U16.lt (Cast.uint64_to_uint16 a) b = U16.lt a16 b)
  && ((b = Cast.uint64_to_uint16 a) = (b = a16))
  && (U16.lt b (Cast.uint64_to_uint16 a) = U16.lt b a16)

let check_u8 (a: U64.t) (b: U8.t) : bool =
  let a8 = Cast.uint64_to_uint8 a in
  ((Cast.uint64_to_uint8 a = b) = (a8 = b))
  && (U8.lt (Cast.uint64_to_uint8 a) b = U8.lt a8 b)
  && ((b = Cast.uint64_to_uint8 a) = (b = a8))
  && (U8.lt b (Cast.uint64_to_uint8 a) = U8.lt b a8)

let main () : FStar.Int32.t =
  if check_u32 0x100000000UL 1ul
  && check_u32 0x100000001UL 1ul
  && check_u32 0x100000002UL 1ul
  && check_u32 0xffffffffffffffffUL 0xfffffffful
  && check_u32 0UL 0ul
  && check_u32 1UL 0ul
  && check_u16 0x10000UL 1us
  && check_u16 0x10001UL 1us
  && check_u16 0x10002UL 1us
  && check_u16 0xffffffffffffffffUL 0xffffus
  && check_u8 0x100UL 1uy
  && check_u8 0x101UL 1uy
  && check_u8 0x102UL 1uy
  && check_u8 0xffffffffffffffffUL 0xffuy
  then 0l
  else 1l
