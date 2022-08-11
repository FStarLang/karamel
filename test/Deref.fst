module Deref

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

let test1 (b: B.buffer bool) : HST.Stack bool
  (fun h -> B.live h b /\ B.length b == 1)
  (fun _ _ _ -> True)
=
  B.index b 0ul

let test2 (b: B.buffer bool) : HST.Stack bool
  (fun h -> B.live h b /\ B.length b == 1)
  (fun _ _ _ -> True)
=
  B.index b C._zero_for_deref

let test3 (b: B.buffer bool) : HST.Stack unit
  (fun h -> True)
  (fun _ _ _ -> True)
= HST.push_frame ();
  let b = B.alloca true 1ul in
  let r1 = B.index b 0ul in
  LowStar.Printf.print_bool r1;
  let r2 = B.index b C._zero_for_deref in
  LowStar.Printf.print_bool r2;
  HST.pop_frame ()

let test4 (b: B.buffer bool) : HST.Stack unit
  (fun h -> True)
  (fun _ _ _ -> True)
= HST.push_frame ();
  let b = B.alloca true 1ul in
  let r1 = B.index b 0ul in
  LowStar.Printf.print_bool r1;
  let r2 = B.index b C._zero_for_deref in
  LowStar.Printf.print_bool r2;
  let _ = test1 b in
  let _ = test2 b in
  HST.pop_frame ()

let main () = C.EXIT_SUCCESS
