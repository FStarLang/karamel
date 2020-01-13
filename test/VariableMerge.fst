module VariableMerge

open FStar.HyperStack.ST

let f #a (x: a): St a =
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

let test2 (): St UInt32.t =
  let x = f 1ul in
  if f true then
    let open FStar.UInt32 in
    let y = f 2ul in
    let z = f (x +%^ 1ul) in
    let a = f (y +%^ 1ul) in
    let b = f (z +%^ a) in
    b -%^ 5ul
  else
    let open FStar.UInt32 in
    let y = f (x +%^ 1ul) in // 2
    let z = f (y +%^ 1ul) in // 3
    let a = f (z +%^ 1ul) in // 4
    let b = f (z +%^ 1ul) in // 4
    a +%^ b -%^ 8ul

let main (): St Int32.t =
  let open FStar.UInt32 in
  let test = test () in
  let test1 = test1 () in
  let test2 = test2 () in
  FStar.Int.Cast.Full.uint32_to_int32 (test +%^ test1 +%^ test2)
