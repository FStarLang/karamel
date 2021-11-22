module TailCalls2

let rec test (a b c: Int32.t): Tot (Int32.t) (decreases Int32.v c) =
  let open FStar.Int32 in
  if c >^ 0l then test b a (c -^ 1l) else b

let main () =
  test 0l 1l 1l
