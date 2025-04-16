module Rustptrfield

noeq type foo = {
  a: bool;
  b: bool & LowStar.Buffer.buffer bool;
}

let main_ () = 0ul
