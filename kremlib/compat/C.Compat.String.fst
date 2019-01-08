module C.Compat.String

module U8 = FStar.UInt8
module U32 = FStar.UInt32

module B = LowStar.Buffer
module M = LowStar.Modifies

open FStar.HyperStack.ST

let zero_free (s: Seq.seq C.Compat.char) =
  forall (i: nat). {:pattern (Seq.index s i)}
    i < Seq.length s - 1 ==> Seq.index s i <> C.Compat.char_of_uint8 0uy

let well_formed (s:Seq.seq C.Compat.char) =
  let l = Seq.length s in
  l <= FStar.UInt.max_int 32 /\
  l >= 1 /\
  Seq.index s (l - 1) = C.Compat.char_of_uint8 0uy /\
  zero_free s

// Need the constructor, otherwise the type abbreviation is substituted at
// extraction-time and print has a signature that talks about sequences
abstract
type t = | S: s:Seq.seq C.Compat.char { well_formed s } -> t

let v (s: t): GTot (s:Seq.seq C.Compat.char{well_formed s}) =
  s.s

let length (s: t): GTot (n:nat{n > 0}) =
  Seq.length s.s

noextract abstract
let get (s: t) (l: U32.t{ U32.v l < Seq.length (v s) }): Pure C.Compat.char
  (requires True)
  (ensures (fun c -> c = Seq.index (v s) (U32.v l)))
=
  Seq.index s.s (U32.v l)

let nonzero_is_lt (i: U32.t) (s: t): Lemma
  (requires (
    U32.v i < length s /\
    get s i <> C.Compat.char_of_uint8 0uy))
  (ensures (U32.v i < length s - 1))
  [SMTPat (get s i)]
=
  ()

(* Stateful combinators *)

// TODO: check statically that the literals don't contain \0
[@ (CPrologue "\
 #define C_Compat_String_of_literal C_String_of_literal\n")]
assume val of_literal: s:Prims.string ->
  Pure t
    (requires True)
    (ensures (fun cs ->
      length cs == normalize_term (List.Tot.length (FStar.String.list_of_string s)) + 1))

noextract
unfold
let (!$) = of_literal

[@ (CPrologue "\
  #define C_Compat_String_t C_String_t\n\
  #define C_Compat_String_print C_String_print\n")]
assume val print: t -> Stack unit
  (fun _ -> true)
  (fun h0 _ h1 -> h0 == h1)

[@ (CPrologue "\
 #define C_Compat_String_strlen C_String_strlen\n")]
assume val strlen (s: t): l:UInt32.t{U32.v l = length s - 1 }

[@ (CPrologue "\
 #define C_Compat_String_memcpy C_String_memcpy\n")]
assume val memcpy (dst: B.buffer UInt8.t) (src: t) (n: U32.t): Stack unit
  (requires (fun h0 ->
    B.live h0 dst /\
    B.length dst = U32.v n /\
    n = strlen src))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst = (
      let s = v src in
      Seq.init (Seq.length s) (fun (i:nat{i<Seq.length s}) ->
        C.Compat.uint8_of_char (Seq.index s i)))))
