module GcTypes

open FStar.HyperStack.ST

module I32 = FStar.Int32

let test (): Stack (list I32.t) (fun _ -> true) (fun _ _ _ -> true) =
  0l :: 1l :: []

let main (): Stack I32.t (fun _ -> true) (fun _ _ _ -> true) =
  match test () with
  | x :: y :: [] ->
      FStar.Int32.(x +%^ y -%^ 1l)
  | _ ->
      1l
