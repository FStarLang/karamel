module C.String

module U8 = FStar.UInt8
module U32 = FStar.UInt32

module B = LowStar.Buffer
module M = LowStar.Modifies

open FStar.HyperStack.ST

let zero_free (s: Seq.seq C.char) =
  forall (i: nat). {:pattern (Seq.index s i)}
    i < Seq.length s - 1 ==> Seq.index s i <> C.char_of_uint8 0uy

let well_formed (s:Seq.seq C.char) =
  let l = Seq.length s in
  l <= FStar.UInt.max_int 32 /\
  l >= 1 /\
  Seq.index s (l - 1) = C.char_of_uint8 0uy /\
  zero_free s

// Need the constructor, otherwise the type abbreviation is substituted at
// extraction-time and print has a signature that talks about sequences
val t : Type0

val v (s: t) : GTot (s:Seq.seq C.char{well_formed s})

val length (s: t): GTot (n:nat{n > 0 /\ n == Seq.length (v s)})

val get (s: t) (l: U32.t{ U32.v l < Seq.length (v s) }): Pure C.char
  (requires True)
  (ensures (fun c -> c = Seq.index (v s) (U32.v l)))

val nonzero_is_lt (i: U32.t) (s: t): Lemma
  (requires (
    U32.v i < length s /\
    get s i <> C.char_of_uint8 0uy))
  (ensures (U32.v i < length s - 1))
  [SMTPat (get s i)]

(* Stateful combinators *)

// TODO: check statically that the literals don't contain \0
val of_literal: s:Prims.string ->
  Pure t
    (requires True)
    (ensures (fun cs ->
      length cs == normalize_term (List.Tot.length (FStar.String.list_of_string s)) + 1))

unfold
let (!$) = of_literal

val print: t -> Stack unit
  (fun _ -> true)
  (fun h0 _ h1 -> h0 == h1)

val strlen (s: t): l:UInt32.t{U32.v l = length s - 1 }

val memcpy (dst: B.buffer UInt8.t) (src: t) (n: U32.t): Stack unit
  (requires (fun h0 ->
    B.live h0 dst /\
    B.length dst = U32.v n /\
    n = strlen src))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst = (
      let s = v src in
      Seq.init (Seq.length s) (fun (i:nat{i<Seq.length s}) ->
        C.uint8_of_char (Seq.index s i)))))
