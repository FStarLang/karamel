module C.Compat.Endianness

open FStar.HyperStack.ST
open FStar.Kremlin.Endianness
open FStar.Buffer

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
  b:buffer UInt8.t{length b == 2} ->
  z:UInt16.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b /\
                           le_to_n (as_seq h1 b) == UInt16.v z))

assume val load16_le:
  b:buffer UInt8.t{length b == 2} ->
  Stack UInt16.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\
                           le_to_n (as_seq h1 b) == UInt16.v z))


assume val store16_be:
  b:buffer UInt8.t{length b == 2} ->
  z:UInt16.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b /\
                           be_to_n (as_seq h1 b) == UInt16.v z))

assume val load16_be:
  b:buffer UInt8.t{length b == 2} ->
  Stack UInt16.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\
                           be_to_n (as_seq h1 b) == UInt16.v z))


assume val store32_le:
  b:buffer UInt8.t{length b == 4} ->
  z:UInt32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b /\
                           le_to_n (as_seq h1 b) == UInt32.v z))

assume val load32_le:
  b:buffer UInt8.t{length b == 4} ->
  Stack UInt32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\
                           le_to_n (as_seq h1 b) == UInt32.v z))


assume val store32_be:
  b:buffer UInt8.t{length b == 4} ->
  z:UInt32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b /\
                           be_to_n (as_seq h1 b) == UInt32.v z))

assume val load32_be:
  b:buffer UInt8.t{length b == 4} ->
  Stack UInt32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\
                           be_to_n (as_seq h1 b) == UInt32.v z))


assume val load64_le:
  b:buffer UInt8.t{length b == 8} ->
  Stack UInt64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\
                           le_to_n (as_seq h1 b) == UInt64.v z))

assume val store64_le:
  b:buffer UInt8.t{length b == 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b /\
                           le_to_n (as_seq h1 b) == UInt64.v z))


assume val load64_be:
  b:buffer UInt8.t{length b == 8} ->
  Stack UInt64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\
                           be_to_n (as_seq h1 b) == UInt64.v z))

assume val store64_be:
  b:buffer UInt8.t{length b == 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b /\
                           be_to_n (as_seq h1 b) == UInt64.v z))


assume val load128_le:
  b:buffer UInt8.t{length b == 16} ->
  Stack UInt128.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\
                           le_to_n (as_seq h1 b) == UInt128.v z))

assume val store128_le:
  b:buffer UInt8.t{length b == 16} ->
  z:UInt128.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b /\
                           le_to_n (as_seq h1 b) == UInt128.v z))


assume val load128_be:
  b:buffer UInt8.t{length b == 16} ->
  Stack UInt128.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\
                           be_to_n (as_seq h1 b) == UInt128.v z))

assume val store128_be:
  b:buffer UInt8.t{length b = 16} ->
  z:UInt128.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b /\
                           be_to_n (as_seq h1 b) == UInt128.v z))
