module InlineTest

type error =
  | E0
  | E1

type optresult 'a 'b =
  | Error of 'a
  | Correct of 'b

type result 'a = optresult error 'a


let f (b:FStar.UInt8.t) : Tot (result (FStar.UInt8.t)) =
  if b = 0uy then Correct 1uy
  else Error E0


let main () =
  match f 0uy with
  | Correct x -> C.EXIT_SUCCESS
  | Error y -> C.EXIT_FAILURE
