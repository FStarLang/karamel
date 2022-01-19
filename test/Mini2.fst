module Mini2

module U32 = FStar.UInt32

let g (x: U32.t) : Tot bool =
 if x `U32.sub` x = 0ul then true else false

let main () = if g 0ul then 0l else 0l
