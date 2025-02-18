module B
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module A = A.Top

let g (x: A.t) : Tot U64.t = A.f Cast.uint32_to_uint64 x

let main () : FStar.HyperStack.ST.St (y: C.exit_code { y == C.EXIT_SUCCESS }) =
  let x : A.t = {
    A.a = 18ul;
    A.b = 42ul;
  }
  in
  let y = g x in
  LowStar.Printf.print_u64 y;
  if y = 1729uL then C.EXIT_SUCCESS else C.EXIT_FAILURE
