module GcTypes

open FStar.HyperStack.ST

module U32 = FStar.UInt32

let test (): Stack (list U32.t) (fun _ -> true) (fun _ _ _ -> true) =
  0ul :: 1ul :: []

let main (): Stack FStar.Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  match test () with
  | x :: y :: [] ->
      FStar.Int.Cast.uint32_to_int32 FStar.UInt32.(x +%^ y -%^ 1ul)
  | _ ->
      FStar.Int.Cast.uint32_to_int32 1ul
