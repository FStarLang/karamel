module TestLib

open FStar.HyperStack.ST
open LowStar.Buffer

module HS = FStar.HyperStack
module Buffer = LowStar.Buffer

(** Some test routines *)

(** Prevent F* from removing the use of a variable. *)
val touch: Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)

(** Check that the two arguments are equal. *)
val check: bool -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val check8: Int8.t -> Int8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val check16: Int16.t -> Int16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val check32: Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val check64: Int64.t -> Int64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val checku8: UInt8.t -> UInt8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val checku16: UInt16.t -> UInt16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val checku32: UInt32.t -> UInt32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val checku64: UInt64.t -> UInt64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)

(** A test routine that takes a string as its first argument; two buffers to
 * compare; the length of the buffers; and exits the program if there is a
 * failure. *)
val compare_and_print: C.String.t ->
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
val unsafe_malloc: l:UInt32.t ->
  Stack (buffer UInt8.t)
    (fun _ -> true)
    (fun h0 b h1 -> live h1 b /\ b `unused_in` h0 /\ length b = FStar.UInt32.v l
      /\ is_eternal_region (frameOf b)
      /\ modifies loc_none h0 h1)

(** Prints: "got error code %d" where %d is the first argument *)
val perr: FStar.UInt32.t -> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))

(** A human-readable debug message specialized for [clock_t] *)
val print_clock_diff: C.clock_t -> C.clock_t -> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))

[@(deprecated "p_null from TestLib; use LowStar.Buffer.null instead")]
val uint8_p_null: buffer UInt8.t

[@(deprecated "p_null from TestLib; use LowStar.Buffer.null instead")]
val uint32_p_null: buffer UInt32.t

[@(deprecated "p_null from TestLib; use LowStar.Buffer.null instead")]
val uint64_p_null: buffer UInt64.t

(** A set of helpers for measuring cycles *)

val cycles: Type0
val cpucycles: unit -> Stack cycles
  (requires (fun h -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))
val print_cycles_per_round: cycles -> cycles -> FStar.UInt32.t -> Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 _ h1 -> h0 == h1))
