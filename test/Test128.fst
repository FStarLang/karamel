module Test128

open FStar.HyperStack.ST

module I32 = FStar.Int32

let y = FStar.UInt128.( mul_wide 0UL 0UL )

let main (): Stack I32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = FStar.UInt128.( y +%^ y ) in
  0l
