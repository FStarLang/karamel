module TestLib

open FStar.HST

assume val touch: Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check: Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
