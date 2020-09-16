module A
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
type t = {a: U32.t; b: U32.t; }
let f (x: t) : Tot U64.t = Cast.uint32_to_uint64 x.a `U64.add` Cast.uint32_to_uint64 x.b
let j (x: t) (b: B.lbuffer U8.t 8) : HST.Stack unit
  (requires (fun h -> B.live h b))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer b) h h'))
= LowStar.Endianness.store64_be b (f x)
