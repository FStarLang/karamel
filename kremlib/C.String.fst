module C.String

module U8 = FStar.UInt8
module U32 = FStar.UInt32

module B = LowStar.Buffer
module M = LowStar.Modifies

open FStar.HyperStack.ST

type t = | S: s:Seq.seq C.char { well_formed s } -> t

let v s = s.s

let length s = Seq.length s.s

let get s l = Seq.index s.s (U32.v l)

let nonzero_is_lt i s = ()

let of_literal _ = admit ()

let print _ = admit ()

let strlen _ = admit ()

let memcpy _ _ _ = admit ()
