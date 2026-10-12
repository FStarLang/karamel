module Rustbufferops

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
open LowStar.BufferOps

type reader = p:B.pointer UInt32.t -> HST.Stack UInt32.t
  (fun h -> B.live h p) (fun _ _ _ -> True)

let apply_reader (f: reader) (p: B.pointer UInt32.t): HST.Stack UInt32.t
  (fun h -> B.live h p) (fun _ _ _ -> True)
= f p

// Exercise both the normalized operations and the retained function bodies.
let main_ (): HST.Stack Int32.t
  (fun _ -> True) (fun _ _ _ -> True)
= HST.push_frame ();
  let p = B.alloca 0ul 1ul in
  p *= 3ul;
  let direct = !*p in
  p *= 7ul;
  let indirect = apply_reader ( !* ) p in
  HST.pop_frame ();
  if direct = 3ul && indirect = 7ul then 0l else 1l
