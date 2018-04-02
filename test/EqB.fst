module EqB

open FStar.HyperStack.ST

open FStar.Buffer

let main (): St Int32.t =
  push_frame ();
  let b1 = createL [ 1; 2; 3 ] in
  let b2 = createL [ 1; 3; 3 ] in
  let b3 = createL [ 1; 2; 3 ] in
  let b4 = createL [ [ 1; 2 ] ] in
  let b5 = createL [ [ 1; 2 ] ] in
  let t1 = eqb b1 b3 3ul in
  let t2 = not (eqb b2 b3 3ul) in
  let t3 = eqb b4 b5 1ul in
  let r =
    if t1 && t2 && t3 then
      0l
    else
      1l
  in
  pop_frame ();
  r
