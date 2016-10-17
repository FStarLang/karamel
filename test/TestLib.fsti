module TestLib

open FStar.ST
open FStar.Buffer

val touch: Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val check: Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val compare_and_print: buffer Int8.t -> buffer UInt8.t -> buffer UInt8.t -> UInt32.t -> Stack unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))
