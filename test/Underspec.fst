module Underspec

open FStar.HyperStack.ST

(* Checking that the *_underspec operators actually extract and run
properly. *)

(* Using this to prevent F*'s normalizers from reducing the tests.
The operations should be there in the C code. *)
irreducible
let four = 4ul

let test1 () : Stack bool (fun _ -> True) (fun _ _ _ -> True) =
  FStar.UInt32.mul_underspec four 2ul = 8ul

let main () =
  if not <| test1 ()
  then 1l
  else 0l