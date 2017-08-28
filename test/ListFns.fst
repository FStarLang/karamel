module ListFns

open FStar.HyperStack.ST

let top_level_mapper (x : int) = x + 1

assume val check_list (#a:Type) : list a -> list a -> ST unit (fun _ -> True) (fun _ _ _ -> True)

let main () : ST unit (fun _ -> True) (fun _ _ _ -> True) =
  let list = List.Tot.map top_level_mapper [1;2;3]
  in check_list list [4;5;6]
