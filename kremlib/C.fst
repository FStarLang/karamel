module C

open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Kremlin.Endianness

module HS = FStar.HyperStack
module U8 = FStar.UInt8

// This module contains a series of bindings that already exist in C. It receives
// a special treatment in Kremlin (no prefixes, no .c/.h generated).
// - If a value already exists (e.g. char or srand), then it is defined via the
//   default #includes.
// - If a value doesn't exist, it is defined in kremlib.h and implemented in
//   kremlib.c (e.g. exit_success, instead of EXIT_SUCCESS).

// The C standard library
assume val srand: UInt32.t -> Stack unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
assume val rand: unit -> Stack Int32.t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
assume val exit: Int32.t -> Stack unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

// This is only to provide a placeholder when needed: this type is not very
// useful, as it is not interconvertible with other pointer types.
assume type intptr_t
assume val nullptr: intptr_t

// Abstract char type, with explicit conversions to/from uint8
assume val char: Type0
assume HasEq_char: hasEq char
assume val char_of_uint8: U8.t -> char
assume val uint8_of_char: char -> U8.t
assume val char_uint8 (c: char): Lemma (ensures (char_of_uint8 (uint8_of_char c) = c))
  [ SMTPat (uint8_of_char c) ]
assume val uint8_char (u: U8.t): Lemma (ensures (uint8_of_char (char_of_uint8 u) = u))
  [ SMTPat (char_of_uint8 u) ]

// Clocks
assume val int: Type0
assume val clock_t: Type0
assume val clock: unit -> Stack clock_t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

// C stdlib; the order of these constructors matters for Wasm
type exit_code = | EXIT_SUCCESS | EXIT_FAILURE

// DEPRECATED
let exit_success : Int32.t = Int32.int_to_t 0
let exit_failure : Int32.t = Int32.int_to_t 1

// Debugging
assume val print_bytes: b:buffer UInt8.t -> len:UInt32.t{UInt32.v len <= length b} -> Stack unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 -> h0 == h1))

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
