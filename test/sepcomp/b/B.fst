module B
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

let g (x: A.t) : FStar.HyperStack.ST.St unit =
  A.f x;
  A.f x

let main () : FStar.HyperStack.ST.St C.exit_code =
  let x : A.t = {
    A.a = 18ul;
    A.b = 42ul;
  }
  in
  g x;
  C.EXIT_SUCCESS
