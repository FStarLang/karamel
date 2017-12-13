module CustomEq

open FStar.HyperStack.ST

type point = {
  x: Int32.t;
  y: Int32.t
}

type t a =
  | A: p1: point -> p2: point -> t a
  | B: a -> t a

let p1 (): Stack point (fun _ -> true) (fun _ _ _ -> true) =
  { x = 0l; y = 1l }

let f (): Stack nat (fun _ -> true) (fun _ _ _ -> true) =
  2

let p2 (): Stack point (fun _ -> true) (fun _ _ _ -> true) =
  { x = 0l; y = f () }

let t1 (): Stack (t Int64.t) (fun _ -> true) (fun _ _ _ -> true) =
  A (p1 ()) (p2 ())

let t2 (): Stack (t Int64.t) (fun _ -> true) (fun _ _ _ -> true) =
  B 1L

let id (#a: Type) (x: a): Stack a (fun _ -> true) (fun _ _ _ -> true) =
  x

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  if p1 () = p2 () then
    1l
  else if t1 () = t2 () then
    3l
  else if id [ 1; 2] = id [ 2; 3 ] then
    4l
  else if p1 () <> p2 () && t1 () <> t2 () && id [ 1; 2 ] <> id [ 2; 3 ] then
    0l
  else
    2l
