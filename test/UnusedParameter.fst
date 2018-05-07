module UnusedParameter

open FStar.HyperStack.ST

type t p =
  | T: x:Int64.t{p x} -> t p

let p = fun _ -> True

let f (): t (fun _ -> True) =
  T 0L

let touch (x: t p): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let main () =
  let x: t p = f () in
  touch x;
  0l
