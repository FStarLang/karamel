module VariableMerge

open FStar.HyperStack.ST

let f (x: UInt32.t): St UInt32.t =
  x

let test (): St UInt32.t =
  let open FStar.UInt32 in
  let x = f 1ul in
  let y = f 2ul in
  let z = f (x +%^ 1ul) in
  let a = f (y +%^ 1ul) in
  let b = f (z +%^ a) in
  b -%^ 5ul

let test1 (): St UInt32.t =
  let open FStar.UInt32 in
  let x = f 0ul in
  let y = f (x +%^ 1ul) in
  let z = f (y +%^ 1ul) in
  let a = f (z +%^ 1ul) in
  let b = f (z +%^ 1ul) in
  a +%^ b -%^ 6ul

let main (): St Int32.t =
  let test = test () in
  let test1 = test1 () in
  FStar.Int.Cast.Full.uint32_to_int32 (test1 `FStar.UInt32.add_mod` test)
