module Wasm6

open FStar.HyperStack.ST

module B = LowStar.Buffer

open LowStar.BufferOps

inline_for_extraction
let fst (x: B.buffer (Int32.t * Int32.t)): Stack Int32.t
  (requires (fun h -> B.live h x /\ B.length x >= 1))
  (ensures (fun h0 _ h1 -> B.modifies B.loc_none h0 h1))
=
  let fst, _ = x.(0ul) in
  fst

inline_for_extraction
let snd (x: B.buffer (Int32.t * Int32.t)): Stack Int32.t
  (requires (fun h -> B.live h x /\ B.length x >= 1))
  (ensures (fun h0 _ h1 -> B.modifies B.loc_none h0 h1))
=
  let _, snd = x.(0ul) in
  snd

(* This exercises proper desugaring of compound literals semantics in Wasm. The
   code below is crafted to generate:
     *x = { fst = x->snd; snd = x->fst }
   which is properly desugared by a C compiler to:
     let *tmp = alloca({ fst = x->snd; snd = x->fst }, 1ul) in
     memcpy(x, tmp, sizeof *x)
   the Wasm backend ought to perform the same transformation. *)
let main (): Stack Int32.t (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca (0l, 1l) 1ul in
  x.(0ul) <- (snd x, fst x);
  let r = snd x in
  pop_frame ();
  r
