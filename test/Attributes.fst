module Attributes

open FStar
open FStar.HyperStack
open FStar.HyperStack.ST

[@ "c_inline" ]
let square (x: UInt32.t): Tot UInt32.t =
  FStar.UInt32.(x *%^ x)

[@ "substitute" ]
let double (x: UInt32.t): Tot UInt32.t =
  FStar.UInt32.(x +%^ x)

let main (): St Int32.t =
  push_frame ();
  let open FStar.UInt32 in
  let x = square 0ul +%^ double 0ul in
  pop_frame ();
  if x = 0ul then 0l else 1l
