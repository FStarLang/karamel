module C.Nullity

module B = FStar.Buffer
module HS = FStar.HyperStack
module HH = FStar.HyperHeap

(* Dealing with possibly-null pointers. *)

val is_null (#a: Type) (b: B.buffer a):
  Tot (ret:bool { ret ==> B.length b = 0})

val null (a: Type):
  b:B.buffer a { b2t (is_null b) }

val null_always_live (#a: Type) (h: HS.mem) (b: B.buffer a):
  Lemma (requires (b2t (is_null b)))
    (ensures (B.live h b))
    [SMTPat (B.live h b)]
