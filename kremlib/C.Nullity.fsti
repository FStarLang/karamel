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
