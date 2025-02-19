module Rusttest

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32

let test2 (b: B.buffer bool) : HST.Stack bool
  (fun h -> B.live h b /\ B.length b == 1)
  (fun _ _ _ -> True)
=
  let x = B.index b C._zero_for_deref in
  AuxA.foo x

let main_ () : HST.Stack I32.t
  (fun _ -> True)
  (fun _ _ _ -> True)
= 
  HST.push_frame ();
  let b = B.alloca true 1ul in
  let _ = test2 b in
  HST.pop_frame ();
  0l
