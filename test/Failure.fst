module Failure

let main (): FStar.HyperStack.ST.St Int32.t =
  LowStar.Failure.failwith "foobar"

