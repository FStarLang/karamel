module TopLevelArray

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open ST
open LowStar.BufferOps

type point2d = {
  x: Int32.t;
  y: Int32.t
}

let x = B.gcmalloc_of_list HS.root [ { x = 1l; y = 0l } ]

let main (): St Int32.t =
  B.recall x;
  (x.(0ul)).y

