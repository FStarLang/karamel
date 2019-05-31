module Wasm11

module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open C.String

private
type point = { x: Int32.t; y: Int32.t }

let f (p: point): St Int32.t =
  p.x

let main (): St Int32.t =
  f ({ x = 0l; y = 1l })
