module Ctypes1

open FStar.Mul
open FStar.UInt
module U32 = FStar.UInt32
module U128 = FStar.UInt128

type point = { x: U32.t; y: U32.t }

let square (x: U32.t): U32.t =
  let open U32 in
  x *%^ x
