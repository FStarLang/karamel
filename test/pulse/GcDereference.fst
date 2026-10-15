module GcDereference

let head (xs: list Int32.t) : Int32.t =
  match xs with
  | [] -> 0l
  | x :: _ -> x
