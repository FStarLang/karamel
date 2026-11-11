module DanglingElse

(* The outer else must not bind to the final inner if after C printing. *)

open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32

let choose (a b c: bool) (p: B.buffer U32.t{B.length p == 1}) :
  Stack U32.t
    (requires fun h -> B.live h p)
    (ensures fun h0 result h1 ->
      B.modifies (B.loc_buffer p) h0 h1 /\
      result == (if a then
                   (if b then 1ul
                    else if c then 2ul
                    else FStar.Seq.index (B.as_seq h0 p) 0)
                 else 3ul))
=
  (if a then
     (if b then B.upd p 0ul 1ul
      else if c then B.upd p 0ul 2ul
      else ())
   else B.upd p 0ul 3ul);
  B.index p 0ul

let test_case (a b c: bool) (expected: U32.t): Stack bool
  (fun _ -> True) (fun _ _ _ -> True)
= push_frame ();
  let p = B.alloca 9ul 1ul in
  let got = choose a b c p in
  let cell = B.index p 0ul in
  let ok = got = expected && cell = expected in
  pop_frame ();
  ok

let main (): Stack Int32.t
  (fun _ -> True) (fun _ _ _ -> True)
= let fff = test_case false false false 3ul in
  let fft = test_case false false true 3ul in
  let ftf = test_case false true false 3ul in
  let ftt = test_case false true true 3ul in
  let tff = test_case true false false 9ul in
  let tft = test_case true false true 2ul in
  let ttf = test_case true true false 1ul in
  let ttt = test_case true true true 1ul in
  if fff && fft && ftf && ftt && tff && tft && ttf && ttt then 0l else 1l
