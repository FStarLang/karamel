module Endianness

open LowStar.Endianness
open LowStar.Buffer
open FStar.HyperStack.ST

let main (): St Int32.t =
  push_frame ();
  let b = alloca 0uy 16ul in
  let z = load128_le b in
  store64_le_i b 0ul 1UL;
  store64_le_i b 8ul 1UL;
  let z' = load128_le b in
  let z' = FStar.UInt128.shift_right z' 64ul in
  let r =
    1ul `FStar.UInt32.sub_mod`
    FStar.Int.Cast.Full.(uint64_to_uint32 (uint128_to_uint64 z'))
  in
  pop_frame ();
  FStar.Int.Cast.Full.uint32_to_int32 r
