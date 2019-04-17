module Wasm10

module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST

type point = { x: UInt32.t; y: UInt32.t }

type twopoints = point * point

let b: (b: B.buffer twopoints { B.length b = 1 /\ B.recallable b }) =
  B.gcmalloc_of_list HS.root [ ({ x = 0ul; y = 1ul }, { x = 2ul; y = 3ul }) ]

let main (): St Int32.t =
  B.recall b;
  let fst, snd = B.index b 0ul in
  if fst.x = 0ul && fst.y = 1ul && snd.x = 2ul && snd.y = 3ul then
    0l
  else
    1l
