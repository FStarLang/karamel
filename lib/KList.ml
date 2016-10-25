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

let make n f =
  let rec make acc n f =
    if n = 0 then
      acc
    else
      make (f (n - 1) :: acc) (n - 1) f
  in
  make [] n f

let find_opt f l =
  let rec find = function
    | [] ->
        None
    | hd :: tl ->
        match f hd with
        | Some x ->
            Some x
        | None ->
            find tl
  in
  find l

let index p l =
  let rec index i l =
    match l with
    | [] ->
        raise Not_found
    | hd :: tl ->
        if p hd then
          i
        else
          index (i + 1) tl
  in
  index 0 l

let assoc_opt k l =
  begin match find_opt (function
    | Some k', v when k' = k ->
        Some v
    | _ ->
        None
  ) l with
  | Some v -> v
  | None -> raise Not_found
  end

