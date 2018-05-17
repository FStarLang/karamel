module EtaStruct

open FStar.HyperStack.ST

type t = | A: Int32.t -> t

let f i: St t = A i

let g = f

let main (): St Int32.t =
  match f 0l with
  | A x -> x
