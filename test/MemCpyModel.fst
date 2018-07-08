// This module tests the -library flag of KreMLin that turns a model into a set
// of abstract definitions suitable for implementing "natively".
module MemCpyModel

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module M  = LowStar.Modifies

open LowStar.BufferOps
open ST

let equal_tail (s1 s2: Seq.seq UInt8.t):
  Lemma
    (requires (
      Seq.length s1 = Seq.length s2 /\
      Seq.length s1 > 0 /\
      Seq.equal (Seq.slice s1 1 (Seq.length s1)) (Seq.slice s2 1 (Seq.length s2)) /\
      Seq.index s1 0 == Seq.index s2 0))
    (ensures (Seq.equal s1 s2))
  [SMTPat (Seq.equal s1 s2)]
=
  assert (Seq.equal (Seq.slice s1 0 1) (Seq.slice s2 0 1));
  let s1' = Seq.append (Seq.slice s1 0 1) (Seq.slice s1 1 (Seq.length s1)) in
  let s2' = Seq.append (Seq.slice s2 0 1) (Seq.slice s2 1 (Seq.length s2)) in
  assert (Seq.equal s1' s2');
  assert (Seq.equal s1 s1');
  assert (Seq.equal s2 s2')

open FStar.Integers

let rec memcpy (dst src: B.buffer UInt8.t) (count: UInt32.t):
  Stack unit
    (requires fun h0 ->
      B.live h0 dst /\ B.live h0 src /\ B.disjoint dst src /\
      B.len dst = count /\ B.len src = count)
    (ensures fun h0 _ h1 -> M.(modifies (loc_buffer dst) h0 h1) /\ B.live h1 dst /\
      Seq.equal (B.as_seq h1 dst) (B.as_seq h0 src))
=
  if count > 0ul then begin
    let dst' = B.offset dst 1ul in
    let src' = B.offset src 1ul in
    memcpy dst' src' (count - 1ul);
    dst.(0ul) <- src.(0ul)
  end
