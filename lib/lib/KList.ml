let rec filter_mapi i f l =
  match l with
  | [] ->
      []
  | x :: l ->
      match f i x with
      | Some x ->
          x :: filter_mapi (i + 1) f l
      | None ->
          filter_mapi (i + 1) f l

let filter_mapi f l =
  filter_mapi 0 f l

let filter_some l = List.filter_map Fun.id l

let rec filter_mask mask l =
  match mask, l with
  | true :: mask, x :: l ->
      x :: filter_mask mask l
  | false :: mask, _ :: l ->
      filter_mask mask l
  | [], [] ->
      []
  | _ ->
      invalid_arg "filter_mask"

let fold_lefti f init l =
  let rec fold_lefti i acc = function
    | hd :: tl ->
        fold_lefti (i + 1) (f i acc hd) tl
    | [] ->
        acc
  in
  fold_lefti 0 init l

let make n f =
  if n < 0 then
    invalid_arg "KList.make";
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

let split i l =
  let rec split acc i l =
    if i = 0 then
      List.rev acc, l
    else match l with
      | hd :: l ->
          split (hd :: acc) (i - 1) l
      | [] ->
          raise (Invalid_argument "split")
  in
  split [] i l

let split_at_last l =
  let all_but_last, last = split (List.length l - 1) l in
  all_but_last, List.hd last

let last l =
  snd (split_at_last l)

let reduce f l =
  List.fold_left f (List.hd l) (List.tl l)

let one l =
  match l with
  | [ x ] -> x
  | _ -> invalid_arg ("one: argument is of length " ^ string_of_int (List.length l))

let max l =
  if List.length l = 0 then
    invalid_arg "max";
  let max = ref (List.hd l) in
  List.iter (fun x -> if x > !max then max := x) (List.tl l);
  !max

let min l =
  if List.length l = 0 then
    invalid_arg "min";
  let min = ref (List.hd l) in
  List.iter (fun x -> if x < !min then min := x) (List.tl l);
  !min

let is_empty = function
  | [] -> true
  | _ -> false
