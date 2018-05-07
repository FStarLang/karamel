module ParamAbbrev

open FStar.HyperStack.ST

type t = Int64.t
type t' = t
type lt = list t
type lt' = list t'

let ft (): Stack lt (fun _ -> true) (fun _ _ _ -> true) =
  []

let g (l: lt): Stack lt' (fun _ -> true) (fun _ _ _ -> true) =
  l

let touch (l: lt'): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  touch (g (ft ()));
  0l
