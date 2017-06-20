module Unsound

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Int32
open TestLib

let f (b: Buffer.buffer Int32.t): Stack Int32.t
  (requires (fun h0 -> Buffer.live h0 b /\ Buffer.length b > 0))
  (ensures (fun h0 _ h1 -> Buffer.live h1 b)) =
  let i = Buffer.index b 0ul in
  Buffer.upd b 0ul (i +%^ 1l);
  i

let g (i: Int32.t): StackInline (Buffer.buffer Int32.t)
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> Buffer.modifies_0 h0 h1)) =
  let _ = i +%^ i in
  Buffer.createL [ 0l ]

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let b = Buffer.createL [ 0l ] in
  let _ = g (f b) in
  check (Buffer.index b 0ul) 1l;
  pop_frame ();
  C.exit_success
