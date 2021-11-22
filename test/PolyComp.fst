module PolyComp

type t a = | A | B of a

let one_t #a (): FStar.HyperStack.ST.St (t a) =
  A

let another_t (): FStar.HyperStack.ST.St (t unit) =
  B ()

let yet_another_t (): FStar.HyperStack.ST.St (t Int32.t) =
  B 0l

let main (): FStar.HyperStack.ST.St Int32.t =
  let b = one_t () = another_t () in
  let b' = one_t () = yet_another_t () in
  if b || b' then
    1l
  else
    0l
