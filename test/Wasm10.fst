module Wasm10

module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open C.String

type point = { x: UInt32.t; y: UInt32.t }

type twopoints = point * point

let b: (b: B.buffer twopoints { B.length b = 1 /\ B.recallable b }) =
  B.gcmalloc_of_list HS.root [ ({ x = 0ul; y = 1ul }, { x = 2ul; y = 3ul }) ]

let s = !$"A constant top-level string"

let string_and_int = s, 42ul

open FStar.Integers

let main (): St Int32.t =
  B.recall b;
  print (fst string_and_int);
  let r = snd string_and_int in
  let first, second = B.index b 0ul in
  if first.x = 0ul && first.y = 1ul && second.x = 2ul && second.y = 3ul && r = 42ul then
    0l
  else
    1l
