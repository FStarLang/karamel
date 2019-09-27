module D

open FStar.Mul
open FStar.UInt
module U32 = FStar.UInt32
open B

let square_d (x: U32.t): U32.t =
  let open U32 in
  x *%^ x

type circle = { c: point; r: U32.t }
