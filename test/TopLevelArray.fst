module TopLevelArray

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open ST
open LowStar.BufferOps

let x = B.gcmalloc_of_list HS.root [ 1l; 0l ]

let main (): St Int32.t =
  B.recall x;
  x.(1ul)

