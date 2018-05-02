module BadMatch

open TestLib

type bar =
| C1 : FStar.UInt32.t -> bar

type baz =
| C2 : bar -> baz

let get_int c2 =
  match c2 with
  | C2 (C1 i) -> i

let main () =
  let b = C2 (C1 10ul) in
  checku32 10ul (get_int b);
  C.EXIT_SUCCESS
