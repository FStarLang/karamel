module OptimizedOption

open FStar.HyperStack.ST

type t = option Int32.t

let f (): St t =
  Some 0l

let main () =
  match f () with
  | Some r -> r
  | None -> 1l
