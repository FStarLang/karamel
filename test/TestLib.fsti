module TestLib

open FStar.ST

val touch: Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
val check: Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
