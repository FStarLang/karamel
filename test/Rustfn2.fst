module Rustfn2

noeq type foo = {
  f: LowStar.Buffer.buffer bool -> bool;
  b: bool;
}

let foo_should_be_copy (f: foo) = f, f

let main_ () = 0ul