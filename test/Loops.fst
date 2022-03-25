module Loops

open FStar
open LowStar.Buffer
open LowStar.BufferOps
open FStar.HyperStack.ST
module UInt32 = FStar.UInt32
module UInt64 = FStar.UInt64

module HS = FStar.HyperStack
module Buffer = LowStar.Buffer

// simple for loop example - note that there is no framing
let sum_to_n (n:UInt32.t) : Stack UInt32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n)) =
  push_frame();
  let ptr_sum = alloca 0ul 1ul in
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
  (ensures (fun h0 r h1 -> r == n /\ modifies loc_none h0 h1)) =
  push_frame();
  let h0 = get() in
  let ptr_sum = alloca 0ul 1ul in
  let _ = C.Loops.interruptible_for 0ul n
    (fun h i done -> live h ptr_sum /\
                  UInt32.v (Seq.index (as_seq h ptr_sum) 0) == i /\
                  done == false /\
                  modifies (loc_buffer ptr_sum) h0 h)
    (fun i -> ptr_sum.(0ul) <- UInt32.(ptr_sum.(0ul) +^ 1ul);
           false) in
  let sum = ptr_sum.(0ul) in
  let h1 = get() in  
  pop_frame();
  sum

let count_to_n (n:UInt32.t{UInt32.v n > 0}) : Stack UInt32.t
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> r == n)) =
  push_frame();
  let ptr_count = alloca 0ul 1ul in
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
  let ptr_count = alloca 0ul 1ul in
  C.Loops.do_while
    (fun h break -> live h ptr_count /\
                  (break ==> False))
    (fun _ -> false);
  let count = ptr_count.(0ul) in
  pop_frame();
  assert (False);
  count

// JP: defining these two as top-level functions to work around "bound variable
// not found"
unfold
let test_pre (b r: buffer UInt32.t) (h: FStar.HyperStack.mem): Type0 =
  live h b /\ live h r /\
  length r = 1 /\ length b = 3 /\
  UInt32.v (Buffer.get h r 0) < Buffer.length b /\
  UInt32.v (Buffer.get h r 0) >= 0

unfold
let test_post (b r: buffer UInt32.t) (test: bool) (h: FStar.HyperStack.mem): Type0 =
  test_pre b r h /\ (test = true ==>
    UInt32.v (Buffer.get h r 0) < Buffer.length b - 1)

#set-options "--max_ifuel 0 --z3rlimit 30"
val square_while: unit -> Stack unit (fun _ -> true) (fun h0 _ h1 -> true)
let square_while () =
  //let open C.Nullity in
  let open FStar.UInt32 in
  push_frame ();
  let b = Buffer.alloca_of_list [ 0ul; 1ul; 2ul ] in
  // JP: createL doesn't work here!
  let r = Buffer.alloca 0ul 1ul in
  // JP: eta-expansions seem necessary for the pre/post
  let test (): Stack bool (requires (fun h -> test_pre b r h)) (ensures (fun _ ret h1 -> test_post b r ret h1)) =
    (!*r) <> 2ul
  in
  let body (): Stack unit (requires (fun h -> test_post b r true h)) (ensures (fun _ _ h1 -> test_pre b r h1)) =
    let h = get () in
    assert (Buffer.live h r /\ Buffer.length r = 1);
    b.(!*r) <- b.(!*r) *%^ b.(!*r);
    r.(0ul) <- !*r +%^ 1ul
  in
  let h = get () in
  assert (
    UInt32.v (Buffer.get h r 0) < Buffer.length b /\
    UInt32.v (Buffer.get h r 0) >= 0
  );
  C.Loops.while #(test_pre b r) #(test_post b r) test body;
  pop_frame ()

(* Same as square_while except testing the while loop with ST effect *)
#set-options "--max_ifuel 0 --z3rlimit 30"
val square_while_st: unit -> ST unit (fun _ -> true) (fun h0 _ h1 -> true)
let square_while_st () =
  //let open C.Nullity in
  let open FStar.UInt32 in
  push_frame ();
  let b = Buffer.alloca_of_list [ 0ul; 1ul; 2ul ] in
  // JP: createL doesn't work here!
  let r = Buffer.alloca 0ul 1ul in
  // JP: eta-expansions seem necessary for the pre/post
  let test (): ST bool (requires (fun h -> test_pre b r h)) (ensures (fun _ ret h1 -> test_post b r ret h1)) =
    (!*r) <> 2ul
  in
  let body (): ST unit (requires (fun h -> test_post b r true h)) (ensures (fun _ _ h1 -> test_pre b r h1)) =
    let h = get () in
    assert (Buffer.live h r /\ Buffer.length r = 1);
    b.(!*r) <- b.(!*r) *%^ b.(!*r);
    r.(0ul) <- !*r +%^ 1ul
  in
  let h = get () in
  assert (
    UInt32.v (Buffer.get h r 0) < Buffer.length b /\
    UInt32.v (Buffer.get h r 0) >= 0
  );
  C.Loops.while_st #(test_pre b r) #(test_post b r) test body;
  pop_frame ()

let test_map (): St unit =
  push_frame ();
  let b = Buffer.alloca 1ul 3ul in
  b.(1ul) <- 2ul;
  b.(2ul) <- 3ul;

  (* An inline example of a map *)
  let out = Buffer.alloca 0ul 3ul in
  let h1 = get () in
  assert (Buffer.live h1 b);
  let f x: Tot UInt32.t = UInt32.(x *%^ x) in
  C.Loops.map out b 3ul f;
  TestLib.checku32 out.(2ul) 9ul;

  (* For64 *)
  let b = Buffer.alloca_of_list [ 1UL; 2UL; 3UL ] in
  C.Loops.for64 0UL 3UL (fun h _ -> Buffer.live h b) (fun i ->
    let i = FStar.Int.Cast.uint64_to_uint32 i in
    let open UInt64 in
    b.(i) <- b.(i) *%^ b.(i)
  );
  TestLib.checku64 b.(2ul) 9UL;

  pop_frame ()

#set-options "--z3rlimit 30 --max_ifuel 0"
val main: unit -> St Int32.t
let main () =
  push_frame ();

  (* Inline test for a for-loop. Todo: move to a separate test. *)
  let b = Buffer.alloca 1ul 3ul in
  b.(1ul) <- 2ul;
  b.(2ul) <- 3ul;
  let h0 = get () in
  assert (Seq.index (Buffer.as_seq h0 b) 2 = 3ul);
  let inv (h1: HS.mem) (i: nat): Type0 =
    Buffer.live h1 b /\ i <= 3 /\ (
    forall j. 0 <= j /\ j < 3 ==> (
      let old = Seq.index (Buffer.as_seq h0 b) j in
      let new_ = Seq.index (Buffer.as_seq h1 b) j in
      if j < i then
        new_ = UInt32.(old *%^ old)
      else
        new_ = old
   ))
  in
  // JP: the refinement has to syntactically be here, it can't be in the
  // requires clause
  let f (i:UInt32.t{UInt32.(0 <= v i /\ v i < 3)}):
    Stack unit
      (requires (fun h ->
        inv h (UInt32.v i)))
      (ensures (fun h_1 _ h_2 ->
        UInt32.(inv h_1 (v i) /\ inv h_2 (v i + 1))))
    =
      let h1 = get () in
      let open UInt32 in
      b.(i) <- b.(i) *%^ b.(i)
  in
  C.Loops.for 0ul 3ul inv f;
  let h1 = get () in
  assert (Seq.index (Buffer.as_seq h1 b) 2 = 9ul);
  assert (Buffer.live h1 b);
  TestLib.checku32 b.(2ul) 9ul;

  (* Call the tests above. *)
  test_map ();
  TestLib.checku32 (count_to_n 10ul) 10ul;
  TestLib.checku32 (sum_to_n 11ul) 11ul;
  TestLib.checku32 (sum_to_n_buf 12ul) 12ul;

  square_while ();
  square_while_st ();

  pop_frame ();

  0l
