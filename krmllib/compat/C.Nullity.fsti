module C.Nullity

module B = FStar.Buffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST

(* Dealing with possibly-null pointers. *)

val is_null (#a: Type) (b: B.buffer a): Pure bool
  (requires True)
  (ensures (fun (ret:bool) -> ret ==> B.length b = 0))

val null (a: Type):
  b:B.buffer a { is_null b }

val null_always_live (#a: Type) (h: HS.mem) (b: B.buffer a):
  Lemma (requires (b2t (is_null b)))
    (ensures (B.live h b))
    [SMTPat (B.live h b)]

val null_always_zero (#a: Type) (b: B.buffer a):
  Lemma (requires (b2t (is_null b)))
    (ensures (B.length b = 0))
    [SMTPat (B.length b)]

(* Useful shorthands for pointers, or maybe-null pointers. *)
type pointer (t: Type0) =
  b:B.buffer t { B.length b = 1 }

type pointer_or_null (t: Type0) =
  b:B.buffer t { if is_null b then True else B.length b = 1 }

let (!*) (#a: Type) (p: pointer a):
  Stack a
  (requires (fun h -> B.live h p))
  (ensures (fun h0 x h1 -> B.live h1 p /\ x == B.get h0 p 0 /\ h1 == h0)) =
  B.index p 0ul

module U32 = FStar.UInt32
module Seq = FStar.Seq
module Heap = FStar.Heap

(* Two pointers with different reads are disjoint *)

let pointer_distinct_sel_disjoint
  (#a: Type)
  (b1: pointer a)
  (b2: pointer a)
  (h: HS.mem)
: Lemma
  (requires (
    B.live h b1 /\
    B.live h b2 /\
    B.get h b1 0 =!= B.get h b2 0
  ))
  (ensures (
    B.disjoint b1 b2
  ))
= if B.frameOf b1 = B.frameOf b2 && B.as_addr b1 = B.as_addr b2
  then begin
    let t1 = B.lseq a (B.max_length b1) in
    let t2 = B.lseq a (B.max_length b2) in
    let r1 : HS.reference t1 = B.content b1 in
    let r2' : HS.reference t2 = B.content b2 in
    assert (B.max_length b1 == B.max_length b2);
    assert (t1 == t2);
    let r2 : HS.reference t1 = r2' in
    HS.reference_distinct_sel_disjoint h (B.content b1) r2
  end
  else ()

