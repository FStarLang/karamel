module C

open FStar.HST

// This module exists a series of bindings that already exist in C. It receives
// a special treatment in Kremlin (no prefixes, no .c/.h generated).
// - If a value already exists (e.g. char or srand), then it is defined via the
//   default #includes.
// - If a value doesn't exist, it is defined in kremlib.h and implemented in
//   kremlib.c (e.g. exit_success, instead of EXIT_SUCCESS).
assume val srand: UInt32.t ->
  Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val rand: unit ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)

assume val char: Type0
assume val int: Type0
assume val exit_success: Int32.t
