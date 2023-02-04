module ExternalEq

open FStar.HyperStack.ST

assume val t: eqtype
assume val mk_pair_t: unit -> St (t & t)

let main () =
  if mk_pair_t () = mk_pair_t () then
    0l
  else if mk_pair_t () <> mk_pair_t () then
    1l
  else
    2l
