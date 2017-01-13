module C

open FStar.ST
open FStar.Buffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

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
assume val exit: Int32.t -> unit

assume val char: Type0
assume val int: Type0
assume val clock_t: Type0

assume val clock: unit -> Stack clock_t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

assume val exit_success: Int32.t
assume val exit_failure: Int32.t

// Note: right now, in Kremlin, the only way to obtain a string is to call
// C.string_of_literal and pass a constant string literal. There are two ways
// we could reveal that strings are 0-terminated buffers of chars:
// - model them as Buffers, which are mutable by default -- this means that
//   C.string_of_literal would have to perform a runtime copy (from const char *
//   to char *), because no one is supposed to mutate the data segment, and
//   this can cause an actual segmentation fault on some architectures
// - add a mutability flag, and model literals as buffers who live in some eternal
//   region of the heap and are immutable -- one could then offer
//   buffer_of_literal that 
// See C11 standard, section 6.4.5. "The multibyte character
// sequence is then used to initialize an array of static storage duration and length just
// sufficient to contain the sequence."
assume type string
assume val string_of_literal: Prims.string -> string

// Note: this assumes a bytes-in, bytes-out semantics for strings in F* which is
// most likely not the case using the F# build of F* -- also, we're confusing
// bytes and strings. Do we want to use better wording?

// Waiting for printf
assume val print_string: string -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))

// Byte-level functions
assume val htole16: UInt16.t -> Tot UInt16.t
assume val le16toh: UInt16.t -> Tot UInt16.t

assume val htole32: UInt32.t -> Tot UInt32.t
assume val le32toh: UInt32.t -> Tot UInt32.t

assume val htole64: UInt64.t -> Tot UInt64.t
assume val le64toh: UInt64.t -> Tot UInt64.t

assume val load64_le:
  b:buffer UInt8.t{length b >= 8} ->
  Stack UInt64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))

assume val store64_le:
  b:buffer UInt8.t{length b >= 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b))

assume val htobe16: UInt16.t -> Tot UInt16.t
assume val be16toh: UInt16.t -> Tot UInt16.t

assume val htobe32: UInt32.t -> Tot UInt32.t
assume val be32toh: UInt32.t -> Tot UInt32.t

assume val htobe64: UInt64.t -> Tot UInt64.t
assume val be64toh: UInt64.t -> Tot UInt64.t

assume val load64_be:
  b:buffer UInt8.t{length b >= 8} ->
  Stack UInt64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))

assume val store64_be:
  b:buffer UInt8.t{length b >= 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b))
