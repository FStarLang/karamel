module D
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module A = A.Top

let k (x: A.t) : Tot U64.t = A.f Cast.uint32_to_uint64 x

let main2 () : FStar.HyperStack.ST.St (y: C.exit_code { y == C.EXIT_SUCCESS }) =
  let x : A.t = {
    A.a = 19ul;
    A.b = 43ul;
  }
  in
  let y = k x in
  LowStar.Printf.print_u64 y;
  if y = 1729uL then C.EXIT_SUCCESS else C.EXIT_FAILURE
