module B
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

let g (x: A.t) : Tot U64.t = A.f x `U64.sub` Cast.uint32_to_uint64 x.A.b

let main () : FStar.HyperStack.ST.St C.exit_code =
  let x : A.t = {
    A.a = 18ul;
    A.b = 42ul;
  }
  in
  LowStar.Printf.print_u64 (g x);
  C.EXIT_SUCCESS
