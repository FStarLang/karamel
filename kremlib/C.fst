module C

open FStar.ST
open FStar.Buffer

// This module contains a series of bindings that already exist in C. It receives
// a special treatment in Kremlin (no prefixes, no .c/.h generated).
// - If a value already exists (e.g. char or srand), then it is defined via the
//   default #includes.
// - If a value doesn't exist, it is defined in kremlib.h and implemented in
//   kremlib.c (e.g. exit_success, instead of EXIT_SUCCESS).
assume val srand: UInt32.t -> Stack unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
assume val rand: unit -> Stack Int32.t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
assume val exit: Int32.t -> unit

assume val char: Type0
assume val int: Type0
assume val clock_t: Type0

assume val clock: unit -> Stack clock_t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

assume val exit_success: Int32.t
assume val exit_failure: Int32.t

assume val htole16: UInt16.t -> Tot UInt16.t
assume val le16toh: UInt16.t -> Tot UInt16.t
assume val htolebe6: UInt16.t -> Tot UInt16.t
assume val be16toh: UInt16.t -> Tot UInt16.t

assume val htole32: UInt32.t -> Tot UInt32.t
assume val le32toh: UInt32.t -> Tot UInt32.t
assume val htobe32: UInt32.t -> Tot UInt32.t
assume val be32toh: UInt32.t -> Tot UInt32.t

assume val htole64: UInt64.t -> Tot UInt64.t
assume val le64toh: UInt64.t -> Tot UInt64.t
assume val htobe64: UInt64.t -> Tot UInt64.t
assume val be64toh: UInt64.t -> Tot UInt64.t

assume val load64:
  b:buffer UInt8.t{length b >= 8} ->
  Stack UInt64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))

assume val store64:
  b:buffer UInt8.t{length b >= 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b))

assume val load32:
  b:buffer UInt8.t{length b >= 4} ->
  Stack UInt32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))

assume val store32:
  b:buffer UInt8.t{length b >= 4} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b))
