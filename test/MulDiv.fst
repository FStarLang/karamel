module MulDiv

open FStar.Mul
// open Lib.IntTypes

// let test (n:size_t) : size_t =
//   [@inline_let]
//   let k = n /. 4ul in
//   4ul *. k


module U32 = FStar.UInt32

let test (n:U32.t) : U32.t =
  [@inline_let]
  let k = U32.div n 4ul in
  U32.mul_mod 4ul k


(* Kremlin extracts above as

uint32_t Example_test(uint32_t n)
{
  return (uint32_t)4U * n / (uint32_t)4U;
}
*)

let main () =
  if test 1ul = 0ul then
    0l
  else
    1l
