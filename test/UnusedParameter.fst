module UnusedParameter

open FStar.HyperStack.ST

type t p =
  | T: x:int{p x} -> t p

let p = fun _ -> True

let f (): t (fun _ -> True) =
  T 0

let touch (x: t p): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let main () =
  let x: t p = f () in
  touch x;
  0l
