module C.Endianness

module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Kremlin.Endianness
open LowStar.BufferOps

// Byte-level functions
assume val htole16: UInt16.t -> Tot UInt16.t
assume val le16toh: UInt16.t -> Tot UInt16.t

assume val htole32: UInt32.t -> Tot UInt32.t
assume val le32toh: UInt32.t -> Tot UInt32.t

assume val htole64: UInt64.t -> Tot UInt64.t
assume val le64toh: UInt64.t -> Tot UInt64.t

assume val htobe16: UInt16.t -> Tot UInt16.t
assume val be16toh: UInt16.t -> Tot UInt16.t

assume val htobe32: UInt32.t -> Tot UInt32.t
assume val be32toh: UInt32.t -> Tot UInt32.t

assume val htobe64: UInt64.t -> Tot UInt64.t
assume val be64toh: UInt64.t -> Tot UInt64.t

assume val store16_le:
  b:B.buffer UInt8.t{B.length b == 2} ->
  z:UInt16.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt16.v z))

assume val load16_le:
  b:B.buffer UInt8.t{B.length b == 2} ->
  Stack UInt16.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt16.v z))


assume val store16_be:
  b:B.buffer UInt8.t{B.length b == 2} ->
  z:UInt16.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt16.v z))

assume val load16_be:
  b:B.buffer UInt8.t{B.length b == 2} ->
  Stack UInt16.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt16.v z))


assume val store32_le:
  b:B.buffer UInt8.t{B.length b == 4} ->
  z:UInt32.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt32.v z))

assume val load32_le:
  b:B.buffer UInt8.t{B.length b == 4} ->
  Stack UInt32.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt32.v z))


assume val store32_be:
  b:B.buffer UInt8.t{B.length b == 4} ->
  z:UInt32.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt32.v z))

assume val load32_be:
  b:B.buffer UInt8.t{B.length b == 4} ->
  Stack UInt32.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt32.v z))


assume val store64_le:
  b:B.buffer UInt8.t{B.length b == 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt64.v z))

assume val load64_le:
  b:B.buffer UInt8.t{B.length b == 8} ->
  Stack UInt64.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt64.v z))


assume val load64_be:
  b:B.buffer UInt8.t{B.length b == 8} ->
  Stack UInt64.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt64.v z))

assume val store64_be:
  b:B.buffer UInt8.t{B.length b == 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt64.v z))


assume val load128_le:
  b:B.buffer UInt8.t{B.length b == 16} ->
  Stack UInt128.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt128.v z))

assume val store128_le:
  b:B.buffer UInt8.t{B.length b == 16} ->
  z:UInt128.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt128.v z))


assume val load128_be:
  b:B.buffer UInt8.t{B.length b == 16} ->
  Stack UInt128.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt128.v z))

assume val store128_be:
  b:B.buffer UInt8.t{B.length b = 16} ->
  z:UInt128.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt128.v z))


let index_32_be (b: B.buffer UInt8.t) (i: UInt32.t):
  Stack UInt32.t
    (requires (fun h ->
      B.live h b /\ B.length b % 4 = 0 /\
      UInt32.v i < B.length b / 4))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (seq_uint32_of_be (B.length b / 4) (B.as_seq h0 b)) (UInt32.v i)))
=
  load32_be (B.sub b FStar.UInt32.(4ul *^ i) 4ul)

let index_32_le (b: B.buffer UInt8.t) (i: UInt32.t):
  Stack UInt32.t
    (requires (fun h ->
      B.live h b /\ B.length b % 4 = 0 /\
      UInt32.v i < B.length b / 4))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (seq_uint32_of_le (B.length b / 4) (B.as_seq h0 b)) (UInt32.v i)))
=
  load32_le (B.sub b FStar.UInt32.(4ul *^ i) 4ul)

let index_64_be (b: B.buffer UInt8.t) (i: UInt32.t):
  Stack UInt64.t
    (requires (fun h ->
      B.live h b /\ B.length b % 8 = 0 /\
      UInt32.v i < B.length b / 8))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (seq_uint64_of_be (B.length b / 8) (B.as_seq h0 b)) (UInt32.v i)))
=
  load64_be (B.sub b FStar.UInt32.(8ul *^ i) 8ul)

let index_64_le (b: B.buffer UInt8.t) (i: UInt32.t):
  Stack UInt64.t
    (requires (fun h ->
      B.live h b /\ B.length b % 8 = 0 /\
      UInt32.v i < B.length b / 8))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (seq_uint64_of_le (B.length b / 8) (B.as_seq h0 b)) (UInt32.v i)))
=
  load64_le (B.sub b FStar.UInt32.(8ul *^ i) 8ul)
