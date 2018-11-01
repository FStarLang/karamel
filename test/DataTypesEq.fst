module DataTypesEq

module SoBuggy = FStar.HyperStack.ST

type t =
  | A: UInt32.t -> t
  | B: unit -> t

let f (): FStar.HyperStack.ST.Stack t (fun _ -> True) (fun _ _ _ -> True) =
  B ()

let main (): FStar.HyperStack.ST.Stack Int32.t (fun _ -> True) (fun _ _ _ -> True) =
  let x = f () in
  if x = (B ()) then
    0l
  else
    1l

