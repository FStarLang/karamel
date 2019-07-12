module Printf

module B = LowStar.Buffer

open LowStar.Printf
open LowStar.BufferOps
open FStar.HyperStack.ST

let main (): St Int32.t =
  push_frame ();
  let a = B.alloca 0uy 4ul in
  a.(1ul) <- 1uy;
  a.(2ul) <- 2uy;
  a.(3ul) <- 3uy;
  printf "LowStar printf\n\
    this is an uint64: %uL\n\
    this is an uint32: %ul\n\
    this is an array: %xuy\n"
    0xffffffffffffffffUL
    0x10111213ul
    4ul a done;
  pop_frame ();
  0l
