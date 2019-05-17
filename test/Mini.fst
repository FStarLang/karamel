module Mini

inline_for_extraction
let f (x: option bool {Some? x}) : Tot bool =
 match x with
 | Some y -> y

module U32 = FStar.UInt32

let g (x: U32.t) : Tot bool =
 if x `U32.sub` x = 0ul then f (Some false) else f None

let main () = if g 0ul then 0l else 0l
