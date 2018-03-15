module Verbatim

open FStar.HyperStack.ST

let x: Int32.t = 0l

[@
  (CPrologue "#define main1 main")
  (CEpilogue "#undef main1")
]
let main1 (): St Int32.t =
  x
