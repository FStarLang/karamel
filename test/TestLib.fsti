module TestLib

open FStar.ST
open FStar.Buffer

val touch: Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val check: Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val compare_and_print: buffer Int8.t -> buffer UInt8.t -> buffer UInt8.t -> UInt32.t -> Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))

(* This function is for testing purposes only: this is an unmanaged, raw
 * pointer that cannot be freed. *)
val unsafe_malloc: UInt32.t -> Stack (buffer UInt8.t) (fun _ -> true) (fun _ _ _ -> true)
val perr: FStar.UInt32.t -> Stack unit (fun _ -> True) (fun _ _ _ -> True)
val print_clock_diff: C.clock_t -> C.clock_t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)

val uint8_p_null: buffer UInt8.t
val uint32_p_null: buffer UInt32.t
val uint64_p_null: buffer UInt64.t
