module A.Base
module U32 = FStar.UInt32
type t = {a: U32.t; b: U32.t; }
let a_le_b (x: t) : Tot bool = x.a `U32.lte` x.b
