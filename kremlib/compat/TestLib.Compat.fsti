module TestLib.Compat

open FStar.HyperStack.ST
open FStar.Buffer

module HS = FStar.HyperStack

(** Some test routines *)

(** Prevent F* from removing the use of a variable. *)
[@ (CPrologue "\
 #define TestLib_Compat_touch TestLib_touch\n")]
val touch: Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)

(** Check that the two arguments are equal. *)
[@ (CPrologue "\
 #define TestLib_Compat_check TestLib_check\n")]
val check: bool -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "\
 #define TestLib_Compat_check8 TestLib_check8\n")]
val check8: Int8.t -> Int8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "\
 #define TestLib_Compat_check16 TestLib_check16\n")]
val check16: Int16.t -> Int16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "\
 #define TestLib_Compat_check32 TestLib_check32\n")]
val check32: Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "\
 #define TestLib_Compat_check64 TestLib_check64\n")]
val check64: Int64.t -> Int64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "\
 #define TestLib_Compat_checku8 TestLib_checku8\n")]
val checku8: UInt8.t -> UInt8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "\
 #define TestLib_Compat_checku16 TestLib_checku16\n")]
val checku16: UInt16.t -> UInt16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "\
 #define TestLib_Compat_checku32 TestLib_checku32\n")]
val checku32: UInt32.t -> UInt32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
[@ (CPrologue "\
 #define TestLib_Compat_checku64 TestLib_checku64\n")]
val checku64: UInt64.t -> UInt64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)

(** A test routine that takes a string as its first argument; two buffers to
 * compare; the length of the buffers; and exits the program if there is a
 * failure. *)
[@ (CPrologue "\
 #define TestLib_Compat_compare_and_print TestLib_compare_and_print\n")]
val compare_and_print: C.Compat.String.t ->
  b1:buffer UInt8.t -> b2:buffer UInt8.t -> l:UInt32.t ->
  Stack unit
    (requires (fun h ->
      let open FStar.UInt32 in
      live h b1 /\ live h b2 /\
      (v l) == Buffer.length b1 /\ (v l) == Buffer.length b2 /\ l >=^ 0ul))
    (ensures (fun h0 _ h1 ->
      h0 == h1 /\
      live h1 b1 /\ live h1 b2 /\
      Buffer.as_seq h1 b1 == Buffer.as_seq h1 b2))

(** This function is for testing purposes only: this is an unmanaged, raw
 * pointer that cannot be freed. *)
[@ (CPrologue "\
 #define TestLib_Compat_unsafe_malloc TestLib_unsafe_malloc\n")]
val unsafe_malloc: l:UInt32.t ->
  Stack (buffer UInt8.t)
    (fun _ -> true)
    (fun h0 b h1 -> live h1 b /\ ~(contains h0 b) /\ length b = FStar.UInt32.v l
      /\ is_eternal_region (frameOf b)
      /\ HyperStack.modifies (Set.singleton (frameOf b)) h0 h1
      /\ HyperStack.modifies_ref (frameOf b) (Set.empty) h0 h1
      /\ (FStar.HyperStack.(Map.domain (HS.get_hmap h0) == Map.domain (HS.get_hmap h1))))

(** Prints: "got error code %d" where %d is the first argument *)
[@ (CPrologue "\
 #define TestLib_Compat_perr TestLib_perr\n")]
val perr: FStar.UInt32.t -> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))

(** A human-readable debug message specialized for [clock_t] *)
[@ (CPrologue "\
 #define TestLib_Compat_print_clock_diff TestLib_print_clock_diff\n")]
val print_clock_diff: C.Compat.clock_t -> C.Compat.clock_t -> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))

[@ (CPrologue "\
 #define TestLib_Compat_uint8_p_null TestLib_uint8_p_null\n")]
val uint8_p_null: buffer UInt8.t

[@ (CPrologue "\
 #define TestLib_Compat_uint32_p_null TestLib_uint32_p_null\n")]
val uint32_p_null: buffer UInt32.t

[@ (CPrologue "\
 #define TestLib_Compat_uint64_p_null TestLib_uint64_p_null\n")]
val uint64_p_null: buffer UInt64.t

(** A set of helpers for measuring cycles *)

val cycles: Type0

[@ (CPrologue "\
  #define TestLib_Compat_cycles TestLib_cycles\n\
  #define TestLib_Compat_cpucycles TestLib_cpucycles\n")]
val cpucycles: unit -> Stack cycles
  (requires (fun h -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))

[@ (CPrologue "\
 #define TestLib_Compat_print_cycles_per_round TestLib_print_cycles_per_round\n")]
val print_cycles_per_round: cycles -> cycles -> FStar.UInt32.t -> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))
