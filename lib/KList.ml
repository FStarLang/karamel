let rec filter_map f l =
  match l with
  | [] ->
      []
  | x :: l ->
      match f x with
      | Some x ->
          x :: filter_map f l
      | None ->
          filter_map f l

let map_flatten f l =
  List.flatten (List.map f l)
