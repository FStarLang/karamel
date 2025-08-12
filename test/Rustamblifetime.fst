module Rustamblifetime
type t = LowStar.Buffer.buffer bool
let foo (x: t) (y: t) : t & t = x, y
let main_ () = 0ul
