module Rusttest

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32

let test2 (b: B.buffer bool) : HST.Stack bool
  (fun h -> B.live h b /\ B.length b == 1)
  (fun _ _ _ -> True)
=
  let x = B.index b C._zero_for_deref in
  let r1 = AuxA.foo x in
  let r2 = AuxB.bar x in
  r1 && r2

let main_ () : HST.Stack I32.t
  (fun _ -> True)
  (fun _ _ _ -> True)
= 
  HST.push_frame ();
  let b = B.alloca true 1ul in
  let _ = test2 b in
  HST.pop_frame ();
  0l
