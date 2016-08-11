module TestLib

open FStar.HST

assume val touch: Int32.t -> Stl unit
assume val check: Int32.t -> Int32.t -> Stl unit
