module Floats

module F32 = FStar.Float32
module F64 = FStar.Float64

let neg32 (x : F32.t) : F32.t = F32.zero `F32.sub` x
let neg64 (x : F64.t) : F64.t = F64.zero `F64.sub` x
