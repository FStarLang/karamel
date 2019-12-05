module VariableMerge

open FStar.HyperStack.ST

let f (x: UInt32.t): St UInt32.t =
  x

let main (): St Int32.t =
  let open FStar.UInt32 in
  let x = f 0ul in
  let y = f (x +%^ 1ul) in
  let z = f (y +%^ 1ul) in
  let a = f (z +%^ 1ul) in
  let b = f (z +%^ 1ul) in
  FStar.Int.Cast.Full.uint32_to_int32 (a +%^ b -%^ 6ul)
