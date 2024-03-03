module Rust4

let f (): HyperStack.ST.St UInt32.t = 1ul

let main_ () =
  if not (f () = 0ul) then
    0l
  else
    1l
