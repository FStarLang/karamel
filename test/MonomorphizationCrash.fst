module MonomorphizationCrash
open Abstract

type pair = {
  fst : t;
  snd : bool
}


assume val mk_t (_:unit) : t

let test (x y:pair) : bool = x = y

let main () =
  let x = mk_t () in
  if test ({fst=x; snd=true}) ({fst=x;snd=false}) then 1l else 0l
