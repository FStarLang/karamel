module Structs

open FStar.HyperStack.ST

type t =
  | T: Int32.t -> Int32.t -> Int32.t -> t

let f (x: t): Stack t (fun _ -> true) (fun _ _ _ -> true) =
  T 1l 2l 3l

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x: t = T 0l 1l 2l in
  let x = f x in
  C.exit_success
