module Rustabbrev2

type foo = { b: bool; }
type bar = { c: foo; }
type baz = { d: bar; }

let f (x: bool) = 0ul
let g (x: baz) = f x.d.c.b

let main_ () = g { d = { c = { b = true } } }