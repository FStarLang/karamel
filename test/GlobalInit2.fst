module GlobalInit2

module U32 = FStar.UInt32
noeq type t = { a: U32.t; b: U32.t; }

assume val g (_: unit) : Tot U32.t

let x = { a = 18ul; b = g (); }
