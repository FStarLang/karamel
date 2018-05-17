module Unsound

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.UInt32
open TestLib

let f (b: Buffer.buffer UInt32.t): Stack UInt32.t
  (requires (fun h0 -> Buffer.live h0 b /\ Buffer.length b > 0))
  (ensures (fun h0 _ h1 -> Buffer.live h1 b)) =
  let i = Buffer.index b 0ul in
  Buffer.upd b 0ul (i +%^ 1ul);
  i

let g (i: UInt32.t): StackInline (Buffer.buffer UInt32.t)
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> Buffer.modifies_0 h0 h1)) =
  let _ = i +%^ i in
  Buffer.createL [ 0ul ]

let main (): Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let b = Buffer.createL [ 0ul ] in
  let _ = g (f b) in
  checku32 (Buffer.index b 0ul) 1ul;
  pop_frame ();
  C.EXIT_SUCCESS
