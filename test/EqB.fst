module EqB

open FStar.Buffer

let main () =
  let b1 = createL [ 1; 2; 3 ] in
  let b2 = createL [ 1; 3; 3 ] in
  let b3 = createL [ 1; 2; 3 ] in
  let b4 = createL [ [ 1; 2 ] ] in
  let b5 = createL [ [ 1; 2 ] ] in
  if eqb b1 b3 3ul && not (eqb b2 b3 3ul) && eqb b4 b5 1ul then
    0l
  else
    1l
