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

let fold_lefti f init l =
  let rec fold_lefti i acc = function
    | hd :: tl ->
        fold_lefti (i + 1) (f i acc hd) tl
    | [] ->
        acc
  in
  fold_lefti 0 init l
