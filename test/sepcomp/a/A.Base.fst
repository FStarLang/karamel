module A.Base
module U32 = FStar.UInt32
type t = {a: U32.t; b: U32.t; }

[@CMacro]
let this_is_a_constant : U32.t = 1729ul

let a_le_b (x: t) : Tot bool = (x.a `U32.lte` x.b)
