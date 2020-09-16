module A
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
type t = {a: U32.t; b: U32.t; }
let f (x: t) : FStar.HyperStack.ST.St unit =
  let y = Cast.uint32_to_uint64 x.a `U64.add` Cast.uint32_to_uint64 x.b in
  LowStar.Printf.print_u64 y
