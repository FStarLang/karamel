module C.String

module U8 = FStar.UInt8
module U32 = FStar.UInt32

open C

private type t' =
  | CString: s:Seq.seq char {
    let l = Seq.length s in
    l <= FStar.UInt.max_int 32 /\
    l >= 1 /\
    Seq.index s (l - 1) = char_of_uint8 0uy
  } -> t'
type t = t'

let v (s: t): GTot (Seq.seq char) =
  s.s

unfold
let length (s: t): GTot nat =
  Seq.length s.s

unfold
let get (s: t) (l: U32.t{ U32.v l < Seq.length s.s }): Tot char =
  Seq.index s.s (U32.v l)

let zero_free (s: t) =
  forall (i: nat). i < Seq.length s.s - 1 ==> Seq.index s.s i <> char_of_uint8 0uy

// TODO: check statically that the literals don't contain \0
assume val of_literal: s:Prims.string ->
  Pure t
    (requires True)
    (ensures (fun cs ->
      zero_free cs /\
      length cs == normalize_term (List.Tot.length (FStar.String.list_of_string s)) + 1))
