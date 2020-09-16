module B
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

let g (x: A.t) : HST.Stack unit (requires (fun _ -> True)) (ensures (fun h _ h' -> B.modifies B.loc_none h h')) =
  HST.push_frame ();
  let b = B.alloca 0uy 8ul in
  A.j x b;
  HST.pop_frame ()

let main () : HST.St C.exit_code =
  let x : A.t = {
    A.a = 18ul;
    A.b = 42ul;
  }
  in
  g x;
  C.EXIT_SUCCESS
