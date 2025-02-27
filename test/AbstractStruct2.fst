module AbstractStruct2
module HS = FStar.HyperStack
module B = LowStar.Buffer

open FStar.HyperStack.ST

[@CAbstractStruct]
noeq
type handle = {
  something: bool;
  another: AbstractStructAbstract.t AbstractStructParameter.param;
}

let init (_:unit) =
  let h = {
    something = false;
    another = AbstractStructAbstract.make AbstractStructParameter.({ param_one = true; param_two = false })
  } in
  B.malloc HS.root h 1ul

open LowStar.BufferOps
open AbstractStructParameter
open AbstractStructAbstract

let main () =
  let p  = init () in
  if (read (!*p).another).param_two then
    1l
  else
    0l
