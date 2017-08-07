module Loops

open FStar
open FStar.Buffer
open FStar.HyperStack.ST
module UInt32 = FStar.UInt32

// simple for loop example - note that there is no framing
let sum_to_n (n:UInt32.t) : Stack UInt32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n)) =
  push_frame();
  let ptr_sum = create 0ul 1ul in
  let _ = C.Loops.interruptible_for 0ul n
    (fun h i done -> live h ptr_sum /\
                  UInt32.v (Seq.index (as_seq h ptr_sum) 0) == i /\
                  done == false)
    (fun i -> ptr_sum.(0ul) <- UInt32.(ptr_sum.(0ul) +^ 1ul);
            false) in
  let sum = ptr_sum.(0ul) in
  pop_frame();
  sum

let sum_to_n_buf (n:UInt32.t) : Stack UInt32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n /\
    modifies_none h0 h1)) =
  push_frame();
  let h0 = get() in
  let ptr_sum = create 0ul 1ul in
  let _ = C.Loops.interruptible_for 0ul n
    (fun h i done -> live h ptr_sum /\
                  UInt32.v (Seq.index (as_seq h ptr_sum) 0) == i /\
                  done == false /\
                  modifies_0 h0 h)
    (fun i -> ptr_sum.(0ul) <- UInt32.(ptr_sum.(0ul) +^ 1ul);
           false) in
  let sum = ptr_sum.(0ul) in
  let h1 = get() in
  lemma_reveal_modifies_0 h0 h1;
  pop_frame();
  sum

let count_to_n (n:UInt32.t{UInt32.v n > 0}) : Stack UInt32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n)) =
  push_frame();
  let ptr_count = create 0ul 1ul in
  C.Loops.do_while
    (fun h break -> live h ptr_count /\
                  (not break ==> UInt32.v (Seq.index (as_seq h ptr_count) 0) < UInt32.v n) /\
                  (break ==> UInt32.v (Seq.index (as_seq h ptr_count) 0) == UInt32.v n))
    (fun _ -> ptr_count.(0ul) <- UInt32.(ptr_count.(0ul) +^ 1ul);
            let sum = ptr_count.(0ul) in
            if UInt32.eq sum n then true else false);
  let count = ptr_count.(0ul) in
  pop_frame();
  count

// this is just an infinite loop
let wait_for_false (n:UInt32.t{UInt32.v n > 0}) : Stack UInt32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n)) =
  push_frame();
  let ptr_count = create 0ul 1ul in
  C.Loops.do_while
    (fun h break -> live h ptr_count /\
                  (break ==> False))
    (fun _ -> false);
  let count = ptr_count.(0ul) in
  pop_frame();
  assert (False);
  count

let main () =
  (* An inline example of a for loop. *)
  let b = Buffer.createL [ 1ul; 2ul; 3ul ] in
  let h0 = get () in
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
  let h1 = get () in
  assert (Seq.index (Buffer.as_seq h1 b) 2 = 9ul);
  let f x = UInt32.(x *%^ x) in

  (* An inline example of a map *)
  let out = Buffer.create 0ul 3ul in
  C.Loops.map out b 3ul f;

  (* Call the tests above. *)
  TestLib.checku32 (count_to_n 10ul) 10ul;
  TestLib.checku32 (sum_to_n 11ul) 11ul;
  TestLib.checku32 (sum_to_n_buf 12ul) 12ul;

  C.exit_success
