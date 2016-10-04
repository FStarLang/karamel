module C

open FStar.HST
open FStar.Buffer

// This module exists a series of bindings that already exist in C. It receives
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
assume val exit_success: Int32.t
assume val exit_failure: Int32.t
