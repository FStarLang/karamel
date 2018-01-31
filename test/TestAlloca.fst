module TestAlloca

open FStar.HyperStack.ST

let size (): St UInt32.t =
  42ul

let main (): St Int32.t =
  push_frame ();
  let b = Buffer.create 0l (size ()) in
  let r = Buffer.index b 41ul in
  pop_frame ();
  r
