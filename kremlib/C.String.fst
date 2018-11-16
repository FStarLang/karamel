module C.String

module U8 = FStar.UInt8
module U32 = FStar.UInt32

module B = LowStar.Buffer
module M = LowStar.Modifies

open FStar.HyperStack.ST

type t = | S: s:Seq.seq C.char { well_formed s } -> t

let v (s: t): GTot (s:Seq.seq C.char{well_formed s}) =
  match s with | S s -> s

let length (s: t): GTot (n:nat{n > 0}) =
  Seq.length s.s

let get (s: t) (l: U32.t{ U32.v l < Seq.length (v s) }): Pure C.char
  (requires True)
  (ensures (fun c -> c = Seq.index (v s) (U32.v l)))
=
  Seq.index s.s (U32.v l)

// TODO
let of_literal s = admit ()
let print s = admit ()
let strlen s = admit ()
let memcpy dst src n = admit ()
