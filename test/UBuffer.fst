module UBuffer

module UB = LowStar.UninitializedBuffer
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer

let test_ub () :HST.St unit =
  let b = UB.ugcmalloc #UInt32.t HS.root 10ul in  //allocate an uninitialized buffer, no initializer
  UB.uupd b 1ul 2ul;  //update at index 1 with value 2
  let j = UB.uindex b 1ul in  //can now project index 1
  assert (j == 2ul);  //and check that the value is 2
  //let j = UB.uindex b 4ul in --> this fails since the index 4 is not yet initialized
  let b1 = B.gcmalloc HS.root 0ul 10ul in  //allocate a different regular buffer
  let h0 = HST.get () in
  UB.ublit b1 2ul b 2ul 3ul;  //copy [2, 5) from regular buffer to [2, 5) of uninitialized buffer
  let h1 = HST.get () in
  let j = UB.uindex b 4ul in  //now 4ul is indexable
  assert (j == 0ul);  //and we can check its value is 0 (from the source buffer)
  let j = UB.uindex b 1ul in  //1ul remains initialized and has the same value as before
  assert (Seq.index (UB.as_seq h0 b) 1 == Seq.index (Seq.slice (UB.as_seq h0 b) 0 2) 1);
  assert (j == 2ul)

let test_ub_stack () :HST.St UInt32.t =
  let b1 :UB.ubuffer UInt32.t = UB.umalloc HS.root 2ul in
  HST.push_frame ();
  let b2 :UB.ubuffer UInt32.t = UB.ualloca 2ul in
  UB.uupd b2 1ul 1ul;
  let t = UB.uindex b2 1ul in
  HST.pop_frame ();
  B.free b1;
  t

let main (): HST.St Int32.t  =
  test_ub ();
  0l
