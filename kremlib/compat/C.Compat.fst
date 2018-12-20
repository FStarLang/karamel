module C.Compat

open FStar.HyperStack.ST

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
  (ensures (fun h0 _ h1 -> h0 == h1))
assume val rand: unit -> Stack Int32.t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))
assume val exit: Int32.t -> Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> False))
// Re-routed to KRML_HOST_EXIT for environments which don't have a libc
assume val portable_exit: Int32.t -> Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> False))

assume type channel
assume val stdout: channel
assume val stderr: channel
assume val fflush: channel -> St Int32.t

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

// C stdlib; the order of these constructors matters for Wasm. When emitting C
// code, this type gets a special case and is not emitted to C.
type exit_code = | EXIT_SUCCESS | EXIT_FAILURE

// Debugging
assume val print_bytes: b:Buffer.buffer UInt8.t -> len:UInt32.t{UInt32.v len <= Buffer.length b} -> Stack unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 -> h0 == h1))

include C.Compat.Endianness
