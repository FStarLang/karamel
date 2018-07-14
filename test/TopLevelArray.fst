module TopLevelArray

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open ST
open LowStar.BufferOps

noeq
type t = {
  x: Int32.t;
  y: (y:B.buffer Int32.t{B.length y = 1 /\ B.recallable y});
  z: C.String.t;
}

// Note: KreMLin will *not* extract this as const char s[] = "whatevs", meaning
// it can't be used within an initializer, so we use inline_for_extraction.
inline_for_extraction
let s = C.String.of_literal "whatevs"

inline_for_extraction
let zero = 0l

let y = B.gcmalloc_of_list HS.root [ zero ]

let x = B.gcmalloc_of_list HS.root [ { x = 1l; y = y; z = s } ]

let g = { x = 1l; y = y; z = s }

let main (): St Int32.t =
  B.recall x;
  B.recall (x.(0ul)).y;
  (x.(0ul)).y.(0ul)

