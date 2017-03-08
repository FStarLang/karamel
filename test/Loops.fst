module Loops

open FStar
open FStar.Buffer
module UInt32 = FStar.UInt32

let main () =
  let b = Buffer.createL [ 1ul; 2ul; 3ul ] in
  let h0 = ST.get () in
  let inv h1 i =
    forall j. 0 <= j /\ j < i ==> (
      let old = Seq.index (Buffer.as_seq h0 b) j in
      let new_ = Seq.index (Buffer.as_seq h1 b) j in
      UInt32.(new_ =^ old *%^ old))
  in
  let f (i:UInt32.t{UInt32.(0 <= v i /\ v i < 3)}):
    Stack unit
      (requires (fun h ->
        inv h (UInt32.v i)))
      (ensures (fun h_1 _ h_2 ->
        UInt32.(inv h_1 (v i) /\ inv h_2 (v i + 1))))
    =
      let open UInt32 in
      b.(i) <- b.(i) *%^ b.(i)
  in
  C.Loops.for 0ul 3ul inv f;
  let h1 = ST.get () in
  assert (Seq.index (Buffer.as_seq h1 b) 2 = 9ul);
  let f x = UInt32.(x *%^ x) in
  let out = Buffer.create 0ul 3ul in
  C.Loops.map f out b 3ul;
  C.exit_success
